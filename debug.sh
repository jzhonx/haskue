#!/usr/bin/env bash

# Ensure at least one argument is provided
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input-file> | show"
  exit 1
fi

# If the first argument is "show", run the file server and exit
if [[ "$1" == "show" ]]; then
  go run tools/fileserv/main.go --file=_debug/output.md
  exit 0
fi

input="$1"
cabal build
gtimeout 0.1s cabal run haskue -- -d -m --show-mutable-args $input 2> _debug/t.log
echo ""
go run tools/logp/main.go -input=_debug/t.log -output=_debug/output.md

# show the size of the output.md
ls -lh _debug/output.md
