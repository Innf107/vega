function internal$replicateArray(count, element) {
    const array = new Array(count)
    for (let i = 0; i < count; i++) {
        array[i] = element
    }
    return array
}

// There currently aren't any operations we do on arrays that couldn't
// also be performed on strings so this is fine. If that changes,
// we need to change this code.
// Also, this returns Utf-16 codepoints, not unicode scalars
// so we'll probably want to adjust it at some point to
// align with the native implementation anyway
function internal$codePoints(string) {
    return string
}