#A: {a: int}

B: {
	// #A only "recursively" closes the #A, and the B via embedding. But {b: c: int} is not closed by #A because no
	// #ident exists for {b: c: int}.
	#A
	b: c: int
}

y: B.b
y: d: 3 // allowed as nothing closes b
