{
	i0: 1 == 2
	i1: 2 == 2
	i2: 2 == 1

	f0: 1.0 == 2.0
	f1: 2.0 == 2.0
	f2: 2.0 == 1.0
	f3: 2.0 == 2
	f4: 2 == 2.0
	f5: 1 == 2.0

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
