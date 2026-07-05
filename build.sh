#!/usr/bin/env bash

# Ensure at least one argument is provided
if [[ $# -lt 1 ]]; then
  echo "Usage: $0 <input-file> | show"
  exit 1
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

if [[ "$1" == "cr" ]]; then
  input="${2:-_debug/_t.cue}"
  cabal run haskue -- -d $input
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
  cabal run haskue -- $input
  exit 0
fi

# If the first argument is "show", run the file server and exit
if [[ "$1" == "show" ]]; then
  cabal run haskue -- show-trace _debug/trace.log
  exit 0
fi

if [[ "$1" == "run" ]]; then
  # if the input is empty, use the path, _debug/_t.cue
  input="${2:-_debug/_t.cue}"
  maxTreeDepth="$3"

  cabal build
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
  profileFlags="$3"

  cabal run --project-file=cabal.project.debug --enable-profiling haskue -- $input +RTS $profileFlags

  echo ""

  exit 0
fi

if [[ "$1" == "build" ]]; then
  cabal build --project-file=cabal.project.debug

  echo ""

  exit 0
fi

if [[ "$1" == "release" ]]; then
  cabal install exe:haskue \
    --project-file=cabal.project.release \
    --builddir=dist-release \
    --installdir=release \
    --install-method=copy

  echo ""

  exit 0
fi

# invalid command
echo "Invalid command: $1"
exit 1
