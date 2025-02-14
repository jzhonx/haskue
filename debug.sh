#!/usr/bin/env bash

# Ensure at least one argument is provided
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input-file> | show"
  exit 1
fi

if [[ "$1" == "ce" ]]; then
  cue eval $2
  exit 0
fi

if [[ "$1" == "cr" ]]; then
  cabal run haskue -- -d $2
  exit 0
fi

if [[ "$1" == "cmp" ]]; then
  echo "---- CUE ----"
  echo ""
  cue eval $2
  echo "---- HASKUE ----"
  echo ""
  cabal run haskue -- $2
  exit 0
fi

# If the first argument is "show", run the file server and exit
if [[ "$1" == "show" ]]; then
  go run tools/fileserv/main.go --file=_debug/output.md
  exit 0
fi

input="$1"
cabal build
# Run the program with the input file and redirect the output to a log file.
gtimeout 0.1s cabal run haskue -- -d -m --show-mutable-args $input 2> _debug/t.log
echo ""
go run tools/logp/main.go -input=_debug/t.log -output=_debug/output.md

# show the size of the output.md
ls -lh _debug/output.md
