// This case tests that a reference to a field in a function node is resolved correctly.
y: A.b
B: {d: 2}
A: B & {
	b: c: int
} // A is a function node that has temporary result because B is a reference and evaluated to mutable result.

("A"): {b: d: string}
