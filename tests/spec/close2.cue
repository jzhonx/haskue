x: close({
	[=~"a"]: int
})

y: x & {
	b: 2 // error: field "b" not allowed in struct
}
