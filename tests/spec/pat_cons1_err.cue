// This tests when the pattern of a constraint is a ref and when the ref's value changes,
// the previously valid value is now invalid.
x: {
	[y.z]: {}
	a: 1 + 2
}

y: {
	z:     string
	("z"): =~"a"
}
