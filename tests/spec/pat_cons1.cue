// This tests when the pattern of a constraint is a ref and when the ref's value changes,
// the previously applied constraint value is removed.
x: {
	[y.z]: {f1: 1}
	a: {f2: 2}
	b: {f3: 3}
}
y: {
	z:     string
	("z"): =~"a"
}
