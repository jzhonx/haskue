x0: {f?: 3} & {f: 3}
x1: {f!: 3} & {f: 3}

x2: {f!: int} & {f: int}
x3: {f!: int} & {f?: <1}
x4: {f!: int} & {f: <=3}

x5: {f!: int} & {f: 3}
x6: {f!: 3} & {f: int}

x7: {f!: 3} & {f: <=4}

// x8: {f?: 1} & {f?: 2}
