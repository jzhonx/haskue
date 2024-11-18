#S: {
	a: c?: bool
}

m: #S & {
	a: c: true // okay
}
