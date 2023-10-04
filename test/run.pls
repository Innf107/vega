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

let for : forall a. (List(a), a -> ()) -> ()
let for(list, f) = 
    if sync then {
        let _ = map(f, list)
    } else {
        let _ = mapConcurrent(f, list)
    }


let baseDirectory = scriptLocal(".")

let testFiles = lines(!find "${baseDirectory}/categories" "-type" "f" "-name" "*.pls")


!stack "build" "--fast"

for(testFiles, \file -> {
    
})

