// #Site:        or(Sites)
// #RioSite:     or(RioSites)
// #RCCSSite:    or(RCCSSites)
// #FTSSite:     or(FTSSites)
// #CanarySite:  or(CanarySites)
// #LabSite:     or(LabSites)
// #Environment: or(Environments)

// Environments represents the make-it-so deployable environments.
// Environments: [for env, _ in EnvironmentsInfo {env}]
// Sites: RioSites
// RioSites: [for env, info in EnvironmentsInfo let isRio = info["rio"] != _|_ if isRio {env}]
// RCCSSites: [for env, info in EnvironmentsInfo let isRCCS = info["rccs"] != _|_ if isRCCS {env}]
// FTSSites: [for env, info in EnvironmentsInfo let isFTS = info["fts"] != _|_ if isFTS {env}]
// CanarySites: [for env, info in EnvironmentsInfo let isCanary = info["canary"] != _|_ if isCanary {env}]
// LabSites: [for env, info in EnvironmentsInfo let isLab = info["lab"] != _|_ if isLab {env}]
// CertbotEnvs: [for env, info in EnvironmentsInfo let isCertbot = info["certbot"] != _|_ if isCertbot {env}]

rio: rio:         true
rccs: rccs:       true
fts: fts:         true
canary: canary:   true
lab: lab:         true
certbot: certbot: true

EnvironmentsInfo: {
	"albq01": rio & fts & rccs
	"atl01":  rio & fts & rccs
	"blu-cd": rio & fts & rccs & lab
	// "blu-qa-int":  rio & fts & lab
	// "blu-qa-next": rio & fts & lab
	// "blu-qa-perf": rio & fts & rccs & lab
	// "blu-qa-sats": rio & fts & lab
	// "brln01":      rio & fts
	// "cgco01":      rio & fts & rccs
	// "cgcy01":      rio & fts
	// "chi01":       rio & fts & rccs
	// "chlw01":      rio & fts
	// "corl01":      rio & fts & rccs
	// "ddtc01":      rio & fts
	// "dnvr01":      rio & fts & rccs
	// "dvtc01":      rio & fts
	// "eden01":      rio & fts & rccs
	// "fox01":       rio & fts & rccs & canary
	// "gma2de01":    rio & fts
	// "gma2it01":                        rio & fts
	// "hahd01":                          rio & fts & rccs
	// "hdc01":                           rio & fts
	// "jack01":                          rio & fts & rccs
	// "katy01":                          rio & fts & rccs
	// "mana02":                          rio & fts & rccs
	// "mdhd01":                          rio & fts & rccs
	// "mimi01":                          rio & fts & rccs
	// "minikube-comcast":                rio & fts
	// "mphs01":                          rio & fts & rccs
	// "mtnk01":                          rio & fts & rccs
	// "nape01":                          rio & fts & rccs & canary
	// "nash01":                          rio & fts & rccs
	// "ncs02":                           rio & fts & rccs
	// "new-jack01":                      rio & fts
	// "new-mana01":                      rio & fts
	// "new-ncs01":                       rio & fts
	// "new-pla01":                       rio & fts
	// "new-tall01":                      rio & fts
	// "ntlk01":                          rio & fts
	// "ntlk01-rio-spinnaker-certbot":    certbot
	// "ntlk01-rio-tools-certbot":        certbot
	// "pla01":                           rio & fts & rccs
	// "port01":                          rio & fts & rccs
	// "qa-perf":                         rio & fts & rccs & lab
	// "qa-perf2":                        rio & fts & lab
	// "rnch01":                          rio & fts & rccs
	// "seat01":                          rio & fts & rccs
	// "sfld01":                          rio & fts & rccs
	// "sjos01":                          rio & fts & rccs
	// "smartsearch01":                   rio & fts
	// "smartsearch01-rio-tools-certbot": certbot
	// "sprnpde01":                       rio & fts
	// "sprnpit01":                       rio & fts
	// "stlk0201":                        rio & fts & rccs
	// "stpm01":                          rio & fts & rccs
	// "tall01":                          rio & fts & rccs & canary
	// "vet-cd01":                        rio & fts & rccs & lab
	// "vet-long01":                      rio & fts & rccs & lab
	// "vet-main01":                      rio & fts & rccs & lab
	// "vet-perf03":                      rio & fts & rccs & lab
	// "vet-qanext01":                    rio & fts & rccs & lab
	// "wlfd01":                          rio & fts & rccs
	// "wner01":                          rio & fts & rccs
}
