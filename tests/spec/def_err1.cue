#S: {
	a: b: string
}

m: #S & {
	a: c: 2 // error, feild not defined in #MyStruct
}
