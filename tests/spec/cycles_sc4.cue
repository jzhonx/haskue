x: #List: {
	head: _
	tail: null | x.#List
}

MyList: x.#List & {head: 1, tail: {head: 2}}
