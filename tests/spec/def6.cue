#A: {a: int}

B: {
	#A
	b: c: int
}

x: B
x: d: 3 // not allowed, as closed by embedded #A
