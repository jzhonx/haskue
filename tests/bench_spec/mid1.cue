// Environments represents the make-it-so deployable environments.
Environments: [for env, _ in EnvironmentsInfo {env}]

rio: rio:         true
rccs: rccs:       true
fts: fts:         true
canary: canary:   true
lab: lab:         true
certbot: certbot: true

EnvironmentsInfo: {
	"albq01":      rio & fts & rccs
	"atl01":       rio & fts & rccs
	"blu-cd":      rio & fts & rccs & lab
	"blu-qa-int":  rio & fts & lab
	"blu-qa-next": rio & fts & lab
	"blu-qa-perf": rio & fts & rccs & lab
	"blu-qa-sats": rio & fts & lab
	"brln01":      rio & fts
	"cgco01":      rio & fts & rccs
	"cgcy01":      rio & fts
}
