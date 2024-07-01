{
	i0: 1 == 2
	i1: 2 == 2
	i2: 2 == 1

	b0: true == false
	b1: true == true
	b2: false == true

	s0: "a" == "b"
	s1: "a" == "a"
	s2: "b" == "a"

	n0: null == null
	n1: null == "a"
	n2: "a" == null
	n3: null == {}
	n4: {} == null
	n5: null == (*1 | 2)
	n6: (*1 | 2) == null
}
