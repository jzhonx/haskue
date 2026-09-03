# Releasing Haskue

The version in `haskue.cabal` is the source of truth. Release tags use the same version prefixed with `v`; for example,
package version `0.1.4` is released as tag `v0.1.4`.

Prepare a new version, commit it, and tag that commit:

```sh
./build.sh bump-version 0.1.5
git add haskue.cabal
git commit -m "Bump version to 0.1.5"
git tag -a v0.1.5 -m "Release v0.1.5"
git push origin main v0.1.5
```

`./build.sh version` prints the package version. `./build.sh check-version v0.1.5` verifies a prospective release tag;
the release workflow performs this check automatically before building artifacts.
