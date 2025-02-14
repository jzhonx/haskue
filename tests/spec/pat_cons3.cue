// It tests both dynamic fields and changing pattern.
x: {
	[y.z]: {f1: 1} // changing pattern
	a: {f2: 2}
	("b"): {f3: 3} // dynamic field
}
y: {
	z:     string
	("z"): =~"a"
}
