c1: {
	a: 1
	{
		b: 2
	}
}
c2: close({
	a: 1
	{
		b: 2
	}
})
// c3 is equivalent to c2. The closed embedding will make the c3 closed.
c3: {
	a: 1
	close({
		b: 2
	})
}
