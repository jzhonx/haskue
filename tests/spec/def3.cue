#D: {
	#OneOf

	c: int // adds this field.
}

#OneOf: {a: int} | {b: int}

D1: #D & {a: 12, c: 22} // { a: 12, c: 22 }
