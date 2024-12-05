// checks if a chain of let statements is correctly resolved.
let a = {
	let ia = ib
	let ib = 1
	z: ia
}

x: a.z
