#!/usr/bin/env polaris
options {
    "--pre-print-cases" as prePrintCases: "Print the name of a test case before running it. This is useful to find infinite loops in tests"
}

module List = import("@std/list.pls")

let testdir = !readlink "-f" (scriptLocal("."))
chdir(testdir)

!stack "build" "--fast"
let vega = !readlink "-f" "../${!stack "path" "--dist-dir"}/build/vega/vega"

let compileTests = lines(!find "compile" "-name" "*.vega")


let compileYmlFile(name) = "name: ${name}\nsource-directory: \".\""

let failures = ref 0
List.for(compileTests, \testFile -> {
    if prePrintCases then {
        print("\e[30m[${testFile}]\e[0m")
    } else {}

    chdir(testdir)

    let testName = !basename "-s" ".vega" testFile

    let errorFile = "${!dirname testFile}/${testName}.error"
    let testKind = try ExpectFail(!bash "-c" "cat ${errorFile} 2>&1") with {
        CommandFailure(_) -> ExpectPass
    }

    !rm "-rf" "./run"
    !mkdir "./run"
    writeFile("./run/vega.yaml", compileYmlFile(testName))
    !cp testFile "./run/Main.vega"

    chdir("./run")
    let testResult = try {
        let _ = !bash "-c" "${vega} build 2>&1"
        Passed
    } with {
        CommandFailure(failure) -> {
            Failed(failure.stdout)
        }
    }
    match (testKind, testResult) {
        (ExpectPass, Passed) -> print("\e[32m[${testFile}]: passed\e[0m")
        (ExpectPass, Failed(output)) -> {
            print("\e[1m\e[31m[${testFile}]: FAILED\e[0m\n\e[31m${output}\e[0m")
            failures := failures! + 1
        }
        (ExpectFail(expectedMessage), Passed) -> {
            print("\e[1m\e[31m[${testFile}]: FAILED\e[0m\n\e[31mTest should have failed to compile. Expected error message:\n${expectedMessage}\e[0m")
            failures := failures! + 1
        }
        (ExpectFail(expectedMessage), Failed(actualMessage)) -> {
            # We don't want to include the exact, machine-dependent path of the file here
            # so we allow error files to use $FILE to refer to it.
            let expectedMessage = regexpReplace("\\$FILE", "${!pwd}/./Main.vega", expectedMessage)

            if (expectedMessage == actualMessage) then {
                print("\e[32m[${testFile}]: passed\e[0m")
            } else {
                print("\e[1m\e[31m[${testFile}]: FAILED\e[0m\n\e[31mExpected error message: ${expectedMessage}\nActual error message: ${actualMessage}\e[0m")
                failures := failures! + 1
            }
        }
    }
})

if (failures! == 0) then {
    print("\n\e[1m\e[32mAll tests passed.\e[0m")
} else {
    print("\n\e[1m\e[31m${failures!}/${List.length(compileTests)} TESTS FAILED\e[0m")
}
