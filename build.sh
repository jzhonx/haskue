#!/usr/bin/env bash

projectRoot="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
cabalFile="$projectRoot/haskue.cabal"

readPackageVersion() {
  awk '
    $1 == "version:" {
      print $2
      found = 1
      exit
    }
    END {
      if (!found) exit 1
    }
  ' "$cabalFile"
}

validateVersion() {
  [[ "$1" =~ ^[0-9]+\.[0-9]+\.[0-9]+(\.[0-9]+)?$ ]]
}

# Ensure at least one argument is provided
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 {version|bump-version|check-version|build|build-wasm|build-show-trace|test|bench-check|bench-update|run|runp|explain|show|release|conv|ce|cmp}"
  exit 1
fi

if [[ "$1" == "version" ]]; then
  set -euo pipefail
  readPackageVersion
  exit 0
fi

if [[ "$1" == "bump-version" ]]; then
  set -euo pipefail

  if [[ $# -ne 2 ]] || ! validateVersion "$2"; then
    echo "Usage: $0 bump-version <major.minor.patch[.revision]>" >&2
    exit 1
  fi

  nextVersion="$2"
  currentVersion="$(readPackageVersion)"
  if [[ "$currentVersion" == "$nextVersion" ]]; then
    echo "Haskue is already at version $nextVersion"
    exit 0
  fi

  updatedCabal="$(mktemp "${TMPDIR:-/tmp}/haskue-cabal.XXXXXX")"
  trap 'rm -f "$updatedCabal"' EXIT
  awk -v version="$nextVersion" '
    $1 == "version:" && !updated {
      sub(/[^[:space:]]+$/, version)
      updated = 1
    }
    { print }
    END {
      if (!updated) exit 1
    }
  ' "$cabalFile" > "$updatedCabal"
  cp "$updatedCabal" "$cabalFile"

  echo "Bumped Haskue from $currentVersion to $nextVersion"
  echo "Commit the change, then create tag v$nextVersion on that commit."
  exit 0
fi

if [[ "$1" == "check-version" ]]; then
  set -euo pipefail

  if [[ $# -ne 2 ]]; then
    echo "Usage: $0 check-version <tag>" >&2
    exit 1
  fi

  releaseTag="${2#refs/tags/}"
  packageVersion="$(readPackageVersion)"
  if [[ "$releaseTag" != v* ]] || ! validateVersion "${releaseTag#v}"; then
    echo "Invalid release tag '$2'; expected v<major.minor.patch[.revision]>" >&2
    exit 1
  fi
  tagVersion="${releaseTag#v}"
  if [[ "$tagVersion" != "$packageVersion" ]]; then
    echo "Release tag $2 does not match Haskue package version $packageVersion" >&2
    exit 1
  fi

  echo "Release tag $2 matches Haskue package version $packageVersion"
  exit 0
fi

if [[ "$1" == "explain" ]]; then
  shift
  explainArgs=("$@")

  # Default to the development input and query when no arguments are given.
  if [[ ${#explainArgs[@]} -eq 0 ]]; then
    explainArgs=(_debug/_t.cue x.a)
  fi

  cabal run --project-file=cabal.project.debug haskue -- explain "${explainArgs[@]}"
  exit 0
fi

if [[ "$1" == "conv" ]]; then
  cd tools/extrtxtar
  go run main.go -input="../../$2" -output="../../_debug/_t.cue"
  cd ../..
  exit 0
fi

if [[ "$1" == "ce" ]]; then
  input="${2:-_debug/_t.cue}"
  cue eval $input
  exit 0
fi

if [[ "$1" == "cmp" ]]; then
  # if the input is empty, use the path, _debug/_t.cue
  input="${2:-_debug/_t.cue}"
  echo "---- CUE ----"
  echo ""
  cue eval $input
  echo "---- HASKUE ----"
  echo ""
  cabal run --project-file=cabal.project.debug haskue -- $input
  exit 0
fi

# If the first argument is "show", run the standalone trace viewer and exit.
if [[ "$1" == "show" ]]; then
  traceFile="${2:-_debug/trace.log}"
  cabal run --project-dir=tools/show-trace haskue-show-trace -- "$traceFile"
  exit 0
fi

if [[ "$1" == "build-show-trace" ]]; then
  cabal build --project-dir=tools/show-trace all

  echo ""

  exit 0
fi

if [[ "$1" == "run" ]]; then
  # if the input is empty, use the path, _debug/_t.cue
  input="${2:-_debug/_t.cue}"
  maxTreeDepth="$3"

  cabal build --project-file=cabal.project.debug exe:haskue
  echo ""
  # Run the program with the input file and redirect the output to a log file.
  if [[ -z "$maxTreeDepth" ]]; then
    cabal run --project-file=cabal.project.debug haskue -- eval -d --trace --trace-output=_debug/trace.log $input 2> _debug/t.log
  else
    cabal run --project-file=cabal.project.debug haskue -- eval -d --trace --trace-output=_debug/trace.log --max-tree-depth $maxTreeDepth $input 2> _debug/t.log
  fi

  echo ""

  # show the size of the log file
  ls -lh _debug/t.log

  exit 0
fi

if [[ "$1" == "runp" ]]; then
  # if the input is empty, use the path, _debug/_t.cue
  input="${2:-_debug/_t.cue}"
  read -r -a profileFlags <<< "${3:--pj}"

  cabal run \
    --project-file=cabal.project.profile \
    --builddir=dist-profile \
    haskue -- eval "$input" +RTS "${profileFlags[@]}" -RTS

  echo ""

  exit 0
fi

if [[ "$1" == "eval" ]]; then
  # if the input is empty, use the path, _debug/_t.cue
  input="${2:-_debug/_t.cue}"
  cabal run --project-file=cabal.project.debug haskue -- eval $input

  echo ""

  # show the size of the log file
  ls -lh _debug/t.log

  exit 0
fi

if [[ "$1" == "build" ]]; then
  set -euo pipefail

  nativeCabalOptions=(--project-file=cabal.project.debug)
  cabal build "${nativeCabalOptions[@]}" exe:haskue
  nativePath="$(cabal list-bin "${nativeCabalOptions[@]}" exe:haskue)"
  mkdir -p bin
  ln -sfn "$nativePath" bin/haskue

  echo "Built bin/haskue -> $nativePath"

  exit 0
fi

if [[ "$1" == "build-wasm" ]]; then
  set -euo pipefail

  wasmEnv="$HOME/.ghc-wasm/env"
  if [[ ! -f "$wasmEnv" ]]; then
    echo "Missing ghc-wasm environment: $wasmEnv" >&2
    exit 1
  fi

  source "$wasmEnv"
  wasmCabalOptions=(
    --project-file=cabal.project.debug
    --with-compiler=wasm32-wasi-ghc
    --with-hc-pkg=wasm32-wasi-ghc-pkg
    --with-hsc2hs=wasm32-wasi-hsc2hs
    --with-haddock=wasm32-wasi-haddock
  )

  cabal build "${wasmCabalOptions[@]}" exe:haskue
  wasmPath="$(cabal list-bin "${wasmCabalOptions[@]}" exe:haskue)"
  mkdir -p bin
  ln -sfn "$wasmPath" bin/haskue.wasm

  echo "Built bin/haskue.wasm -> $wasmPath"

  exit 0
fi

if [[ "$1" == "test" ]]; then
  cabal test --project-file=cabal.project.debug

  echo ""

  exit 0
fi

if [[ "$1" == "bench-update" ]]; then
  set -euo pipefail

  projectRoot="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  baseline="$projectRoot/tests/bench_spec/spec-baseline.json"
  result="$(mktemp "${TMPDIR:-/tmp}/haskue-spec-benchmark.XXXXXX")"
  formattedResult="$(mktemp "${TMPDIR:-/tmp}/haskue-spec-benchmark-formatted.XXXXXX")"
  trap 'rm -f "$result" "$formattedResult"' EXIT

  if ! command -v python3 >/dev/null 2>&1; then
    echo "bench-update requires python3" >&2
    exit 1
  fi

  cabal bench spec \
    --project-file=cabal.project.release \
    --benchmark-options="--json $result"

  python3 -m json.tool "$result" "$formattedResult"
  mv -f "$formattedResult" "$baseline"
  trap - EXIT
  echo "Updated $baseline"

  exit 0
fi

if [[ "$1" == "bench-check" ]]; then
  set -euo pipefail

  tolerancePercent="${2:-20}"
  projectRoot="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
  baseline="$projectRoot/tests/bench_spec/spec-baseline.json"
  reportProcessor="$projectRoot/tests/bench_spec/process_report.py"
  result="$(mktemp "${TMPDIR:-/tmp}/haskue-spec-benchmark.XXXXXX")"
  trap 'rm -f "$result"' EXIT

  if ! command -v python3 >/dev/null 2>&1; then
    echo "bench-check requires python3" >&2
    exit 1
  fi

  if [[ ! -f "$baseline" ]]; then
    echo "Missing benchmark baseline: $baseline" >&2
    echo "Run ./build.sh bench-update to create it." >&2
    exit 1
  fi

  cabal bench spec \
    --project-file=cabal.project.release \
    --benchmark-options="--json $result"

  python3 "$reportProcessor" \
    "$baseline" \
    "$result" \
    --tolerance-percent "$tolerancePercent"

  exit 0
fi

if [[ "$1" == "release" ]]; then
  set -euo pipefail

  wasmEnv="$HOME/.ghc-wasm/env"
  if [[ ! -f "$wasmEnv" ]]; then
    echo "Missing ghc-wasm environment: $wasmEnv" >&2
    exit 1
  fi

  # Remove unused code sections with the platform's linker.
  releaseGhcOptions=()
  case "$(uname -s)" in
    Darwin)
      releaseGhcOptions+=(--ghc-options="-optl-Wl,-dead_strip")
      ;;
    Linux)
      releaseGhcOptions+=(--ghc-options="-optl-Wl,--gc-sections")
      ;;
  esac

  cabal install exe:haskue \
    --project-file=cabal.project.release \
    "${releaseGhcOptions[@]}" \
    --builddir=dist-release \
    --overwrite-policy=always \
    --installdir=release \
    --install-method=copy

  source "$wasmEnv"
  wasmReleaseOptions=(
    --project-file=cabal.project.release
    --builddir=dist-release
    --with-compiler=wasm32-wasi-ghc
    --with-hc-pkg=wasm32-wasi-ghc-pkg
    --with-hsc2hs=wasm32-wasi-hsc2hs
    --with-haddock=wasm32-wasi-haddock
  )

  cabal build "${wasmReleaseOptions[@]}" exe:haskue
  wasmReleasePath="$(cabal list-bin "${wasmReleaseOptions[@]}" exe:haskue)"
  cp "$wasmReleasePath" release/.haskue.wasm.tmp
  mv -f release/.haskue.wasm.tmp release/haskue.wasm

  echo "Released release/haskue"
  echo "Released release/haskue.wasm"

  exit 0
fi

# invalid command
echo "Invalid command: $1"
exit 1
