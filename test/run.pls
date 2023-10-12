#!/usr/bin/env polaris
options {
    "-s" "--sync" as sync: "Run tests synchronously"
}

# TODO: I really need a usable package system in Polaris
let map(f, list) = [f(x) | let x <- list]

let mapConcurrent(f, list) = {
    let promises = [async f(x) | let x <- list]
    [await promise | let promise <- promises]
}

let foldr(cons, nil, list) = match list {
    [] -> nil
    (x :: xs) -> cons(x, foldr(cons, nil, xs))
}
let length(list) = foldr(\_ y -> y + 1, 0, list)

let for : forall a. (List(a), a -> ()) -> ()
let for(list, f) = 
    if sync then {
        let _ = map(f, list)
    } else {
        let _ = mapConcurrent(f, list)
    }


let testFiles = lines(!find (scriptLocal("categories")) "-type" "f" "-name" "*.vega")

let doesFileExist(file) = try {
    !test "-f" file
    true
} with {
    CommandFailure(_) -> false
}

!stack "build" "--fast"

let evalTest(file) = {
    try {
        let result = !stack "exec" "vega" file
        Success(result)
    } with {
        CommandFailure(details) -> Failure(details.stdout)
    }
}

let parseExpectation(file) = {
    match regexpMatchGroups("EXPECT:\\s*(\\S+)", !cat file) {
        [[_, expectation]] -> RunExpectation(expectation)
        _ -> {
            # This is not a run test so it has to be an error test
            let errorFile = (!dirname file) ~ "/" ~ (!basename "-s" ".vega" file) ~ ".error"
            if doesFileExist(errorFile) then
                FailExpectation(!cat errorFile)
            else
                fail("No expectations in test file ${file}")
        }
    }
}

let errors = ref 0
let success(file, testType) = {
    let testTypePrefix = match testType {
        "" -> ""
        _ -> "\e[1m(${testType})\e[0m\e[32m"
    }

    # workaround for that annoying bug where string interpolation only works once
    print("\e[32m[${file}]" ~ "${testTypePrefix}: passed")
}
let failure(file, testType, failureType, details) = {
    let testTypePrefix = match testType {
        "" -> ""
        _ -> "\e[1m(${testType})\e[0m\e[31m\e[1m"
    }

    let detailMessage = match details {
        Nothing -> ""
        ExpectedVsActual(details) ->
            "\nExpected:\n\e[0m${details.expected}\n\e[0m\e[31mActual:\n\e[0m" ~ "${details.actual}\e[0m"
        ErrorMessage(message) ->
            "\n${message}\e[0m"
    }

    # workaround for that annoying bug where string interpolation only works once
    print("\e[31m\e[1m[${file}]" ~ "${testTypePrefix}: FAILED: " ~ "${failureType}\e[0m\e[31m" ~ "${detailMessage}\e[0m")

    errors := errors! + 1
}

for(testFiles, \file -> {
    let expectation = parseExpectation(file)

    match expectation {
        RunExpectation(expectedResult) -> {
            match evalTest(file) {
                Success(result) -> {
                    if result == expectedResult then {
                        success(file, "")
                    } else {
                        failure(file, "", "Mismatched Result", ExpectedVsActual({ expected = expectedResult, actual = result }))
                    }
                }
                Failure(message) -> failure(file, "", "Evaluation Failure", ErrorMessage(message))
            }
        }
        FailExpectation(expectedError) -> {
            match evalTest(file) {
                Success(result) -> failure(file, "Fail", "Invalid Success", Nothing)
                Failure(message) -> {
                    if message == expectedError then {
                        success(file, "Fail")
                    } else {
                        failure(file, "Fail", "Mismatched Error Message", ExpectedVsActual({ expected = expectedError, actual = message }))
                    }
                }
            }
        }
    }
})

if errors! == 0 then {
    print("\e[32mAll tests passed successfully")
} else {
    print("\e[31m\e[1m${errors!}/" ~ "${length(testFiles)} Tests failed")
}

