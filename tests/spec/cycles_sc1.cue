// acyclic
y: {
	f: h: g
	g: _
}
// acyclic
x: {
	f: _
	g: f
}
// introduces structural cycle
z: x & y
