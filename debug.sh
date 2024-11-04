# 
# The argument is the path to the input file.

args=("$@")
input=${args[0]}

cabal build
gtimeout 0.07s cabal run haskue -- -d -m $input 2> t.log
echo ""
go run ../haskue-tools/logp/main.go -input=t.log
