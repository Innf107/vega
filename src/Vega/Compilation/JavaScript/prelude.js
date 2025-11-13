function internal$replicateArray(count, element) {
    const array = new Array(count)
    for (let i = 0; i < count; i++) {
        array[i] = element
    }
    return array
}

function internal$codePoints(string) {
    const array = new Array(string.length)
    for (let i = 0; i < string.length; i++) {
        // TODO: this doesn't quite work with non-ascii characters
        array[i] = string.charCodeAt(i)
    }
    return array
}

function internal$readArray(array, index) {
    if (index < 0 || index >= array.length) {
        throw new Error("readArray: Index " + index + " out of range for array of size " + array.length)
    }
    return array[index]
}