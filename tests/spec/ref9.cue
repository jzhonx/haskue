// this tests that chained references are resolved correctly.
a: x.z // simple substitution would not work here.
x: {
	d: 1
	z: d
}
