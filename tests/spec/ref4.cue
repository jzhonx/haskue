a: {
	place:    string
	greeting: place
}
// dep: a.place -> a.greeting

// referencing a will make dependencies change.
// b.place -> b.greeting
b: a & {place: "world"}
c: a & {place: "you"}
