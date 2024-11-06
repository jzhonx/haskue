{
	// referencing a cycle
	x: {
		a: a
		b: a
	}
	y: {
		a: a
		b: a
		b: 2
	}
	z: {
		a: a
		b: a
		a: 2
	}
	dfa: "a"
	z2: {
		a: a
		b: a
		// dynamically add a field to break the cycle
		(dfa): 2
	}
}
