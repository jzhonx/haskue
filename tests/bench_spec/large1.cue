#Type_A: or(As)
#Type_B: or(Bs)
#Type_C: or(Cs)
#Type_D: or(Ds)
#Type_E: or(Es)
#Type_F: or(Fs)
#Type_1: or(Es)
#Type_2: or(Gs)

// Environments represents the make-it-so deployable environments.
As: [for env, info in envInfo let x = info["a"] != _|_ if x {env}]
Bs: [for env, info in envInfo let x = info["b"] != _|_ if x {env}]
Cs: [for env, info in envInfo let x = info["c"] != _|_ if x {env}]
Ds: [for env, info in envInfo let x = info["d"] != _|_ if x {env}]
Es: [for env, info in envInfo let x = info["e"] != _|_ if x {env}]
Fs: [for env, info in envInfo let x = info["f"] != _|_ if x {env}]
Envs: [for env, _ in envInfo {env}]
Gs: As

a: a: true
b: b: true
c: c: true
d: d: true
e: e: true
f: f: true

envInfo: {
	"x-0":  a & c & b
	"x-1":  a & c & b
	"x-2":  a & c & b & e
	"x-3":  a & c & e
	"x-4":  a & c & e
	"x-5":  a & c & b & e
	"x-6":  a & c & e
	"x-7":  a & c
	"x-8":  a & c & b
	"x-9":  a & c
	"x-10": a & c & b
	"x-11": a & c
	"x-12": a & c & b
	"x-13": a & c
	"x-14": a & c & b
	"x-15": a & c
	"x-16": a & c & b
	"x-17": a & c & b & d
	"x-18": a & c
	"x-19": a & c
	"x-20": a & c & b
	"x-21": a & c
	"x-22": a & c & b
	"x-23": a & c & b
	"x-24": a & c & b
	"x-25": a & c & b
	"x-26": a & c & b
	"x-27": a & c
	"x-28": a & c & b
	"x-29": a & c & b
	"x-30": a & c & b & d
	"x-31": a & c & b
	"x-32": a & c & b
	"x-33": a & c
	"x-34": a & c
	"x-35": a & c
	"x-36": a & c
	"x-37": a & c
	"x-38": a & c
	"x-39": f
	"x-40": f
	"x-41": a & c & b
	"x-42": a & c & b
	"x-43": a & c & b & e
	"x-44": a & c & e
	"x-45": a & c & b
	"x-46": a & c & b
	"x-47": a & c & b
	"x-48": a & c & b
	"x-49": a & c
	"x-50": f
	"x-51": a & c
	"x-52": a & c
	"x-53": a & c & b
	"x-54": a & c & b
	"x-55": a & c & b & d
	"x-56": a & c & b & e
	"x-57": a & c & b & e
	"x-58": a & c & b & e
	"x-59": a & c & b & e
	"x-60": a & c & b & e
	"x-61": a & c & b
	"x-62": a & c & b
}
