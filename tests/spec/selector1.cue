{
	// this is the example from the cuelang spec
	T: {
		x:     1
		y:     3
		"x-y": 4
	}
	a: T.x     // 1
	b: T.y     // 3
	c: T.z     // _|_ // field 'z' not found in T
	d: T."x-y" // 4
	e: {a: 1 | *2} | *{a: 3 | *4}
	f: e.a // 4 (default value)
}
