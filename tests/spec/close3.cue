// successful cases
c1: {
	x: close({
		[=~"a"]: int
	})

	y: x & {
		a: 1
	}
}
// c2: {
// 	x: close({
// 		[=~"a"]: int
// 	})
//
// 	y: x & close({
// 		a: 1
// 	})
// }
// c3: {
// 	x: close({
// 		[=~"a"]: int
// 	})
//
// 	y: close({
// 		a: 1
// 	})
//
// 	z: x & y
// }
