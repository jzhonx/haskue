// infinite evaluation
f: {
	n: int
	out: n + (f & {n: 1}).out
}
