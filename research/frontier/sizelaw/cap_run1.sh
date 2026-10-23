#!/bin/zsh
s=$1; shift; tag=$(echo "$@" | tr ' ' '_')_s$s
cd /private/tmp/claude-502/-Users-dogaozden-AI-Projects-degree-diameter/31a2fcff-fd6b-4c01-b1b7-05c9b8d9f143/scratchpad/sl
./haar_gen3 7 8 90 $s 8 cap/$tag.sol "$@" > cap/$tag.log 2>&1
