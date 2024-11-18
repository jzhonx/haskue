#MyStruct: {
	sub: field: string
}

#MyStruct: {
	sub: enabled?: bool
}

myValue: #MyStruct & {
	sub: feild:   2    // error, feild not defined in #MyStruct
	sub: enabled: true // okay
}
