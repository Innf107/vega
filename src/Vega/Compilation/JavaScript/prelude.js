function internal$replicateArray(count, element) {
    const array = new Array(count)
    for (let i = 0; i < count; i++) {
        array[i] = element
    }
    return array
}
