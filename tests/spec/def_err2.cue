#D: {
	#OneOf

	c: int // adds this field.
}

#OneOf: {a: int} | {b: int}

D2: #D & {a: 12, b: 33} // _|_ // cannot define both `a` and `b`
