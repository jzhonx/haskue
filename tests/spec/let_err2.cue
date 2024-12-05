// redeclared in the same block (y has been declared in the top block)
y: 1
x: {
  let y = 2
  z: y
}
