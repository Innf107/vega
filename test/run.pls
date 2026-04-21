#!/usr/bin/env polaris
options {
    "--pre-print-cases" as prePrintCases: "Print the name of a test case before running it. This is useful to find infinite loops in tests"
    "--backend" (*) as backendStrings: "The backend to run tests on. Can be specified multiple times. 'all' will run all backends. Default: 'all'"
    "--hide-passing" as hidePassing: "Only print immediate output for failing tests"
}

module List = import("@std/list.pls")

let parseBackends(backends, strings) = match strings {
    [] -> backends
    (backendString :: rest) -> {
        let backends = match backendString {
            "all" -> { release = true, javascript = true }
            "release" -> { backends with release = true }
            "javascript" -> { backends with javascript = true }
            _ -> fail("Invalid backend '${backendString}'. Possible values are 'all', 'release', 'javascript'")
        }
        parseBackends(backends, rest)
    }
}

let backendRecord = match backendStrings {
    [] -> { release = true, javascript = true }
    _ -> parseBackends({release = false, javascript = false}, backendStrings)
}
let backends = {
    List.concatMap(\(name, active) -> if active then [name] else [], 
        [ (Release, backendRecord.release)
        , (JavaScript, backendRecord.javascript)
        ])
}

type Backend = < Release, JavaScript >
let backendToString(backend) = match backend {
    Release -> "release"
    JavaScript -> "javascript"
}

module List = import("@std/list.pls")

let testdir = !readlink "-f" (scriptLocal("."))
chdir(testdir)

!stack "build" "--fast"
let vega = !readlink "-f" "../${!stack "path" "--dist-dir"}/build/vega/vega"

let compileTests = lines(!find "compile" "-name" "*.vega")


let compileYmlFile(name, backend) = "name: ${name}\nsource-directory: \".\"\nbackend: ${backendToString(backend)}"

let parseTestKind(testFile) = {
    let type_ = try { trim(!grep "-Po" "(?<=type:).+" testFile)} with {
        CommandFailure(_) -> fail("${testFile}: Missing test type specification")
    }

    match type_ {
        "error" -> {
            let testName = !basename "-s" ".vega" testFile
            let errorFile = "${!dirname testFile}/${testName}.error"
            try ExpectFail(!bash "-c" "cat ${errorFile} 2>&1") with {
                CommandFailure(_) -> fail("${testFile}: Missing error file ${errorFile}")
            }
        }
        "compile" -> ExpectCompile
        _ -> {
            match regexpMatchGroups("print\\((.*)\\)", type_) {
                [[_, expectation]] -> ExpectPrint(expectation)
                _ -> fail("${testFile}: Invalid test type ${type_}")
            } 
        }
    }
}

let runCompiledProgram(backend, testName) = match backend {
    Release -> {
        !./a.out
    }
    JavaScript -> {
        !node "${testName}.js"
    }
}

let runTest : (Backend, String) -> < Passed, Failed(String) >
let runTest(backend, testFile) = {
    chdir(testdir)

    let testName = !basename "-s" ".vega" testFile

    let testKind = parseTestKind(testFile)

    !rm "-rf" "./run"
    !mkdir "./run"
    writeFile("./run/vega.yaml", compileYmlFile(testName, backend))
    !cp testFile "./run/Main.vega"

    chdir("./run")
    let compileResult = try {
        let _ = !bash "-c" "${vega} build 2>&1"
        Compiled
    } with {
        CommandFailure(failure) -> {
            CompilerError(failure.stdout)
        }
    }
    match testKind {
        ExpectCompile -> match compileResult {
            Compiled -> Passed
            CompilerError(output) -> Failed("\e[31m${output}")
        }
        ExpectFail(expectedMessage) -> match compileResult {
            Compiled -> Failed("\e[31m\e[1mTest should have failed to compile. Expected error message:\n\e[0m\e[31m${expectedMessage}\e[0m")
            CompilerError(actualMessage) -> {
                # We don't want to include the exact, machine-dependent path of the file here
                # so we allow error files to use $FILE to refer to it.
                let expectedMessage = regexpReplace("\\$FILE", "${!pwd}/./Main.vega", expectedMessage)
                if (expectedMessage == actualMessage) then {
                    Passed
                } else {
                    Failed("\e[0m\n\e[31m\e[1mExpected error message:\e[0m\e[31m ${expectedMessage}\n\e[1mActual error message:\e[0m\e[31m ${actualMessage}\e[0m")
                }
            }
        }
        ExpectPrint(expectation) -> match compileResult {
            CompilerError(output) -> Failed("\e[31m${output}")
            Compiled -> {
                let actualOutput = runCompiledProgram(backend, testName)
                if (actualOutput == expectation) then {
                    Passed
                } else {
                    Failed("\e[0m\e[31m\e[1mExpected:\e[0m\e[31m ${expectation}\n\e[0m\e[31m\e[1m  Actual:\e[0m\e[31m ${actualOutput}")
                }
            }
        }
    }
}

let numberOfBackends = List.length(backends)

let failures = ref 0
List.for(compileTests, \testFile -> {
    if prePrintCases then {
        print("\e[30m[${testFile}]\e[0m")
    } else {}

    let failuresForThisTest = List.filterMap(\backend -> 
        match runTest(backend, testFile) {
            Passed -> Nothing
            Failed(message) -> Just((backend, message))
        }, backends)
    match failuresForThisTest {
        [] -> if not hidePassing then {
            print("\e[32m[${testFile}]: passed\e[0m")
        } else {}
        _ -> {
            failures := failures! + 1
            print("\e[1m\e[31m[${testFile}]: FAILED on ${List.length(failuresForThisTest)}/${numberOfBackends} backends\e[0m")
            List.for(failuresForThisTest, \(backend, message) -> {
                print("\e[1m\e[31m[${backendToString(backend)}]:\e[0m ${message}")
            })
        }
    }


})

if (failures! == 0) then {
    print("\n\e[1m\e[32mAll tests passed.\e[0m")
} else {
    print("\n\e[1m\e[31m${failures!}/${List.length(compileTests)} TESTS FAILED\e[0m")
}
