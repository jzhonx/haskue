x: close({
	a: 1
})

y: x & {
	b: 2 // error: field "b" not allowed in struct.
}
