#!/bin/bash
# usage: check.sh EDGES  -> score37 line, and apsp check if far=0
f=$1
out=$(../bin/score37 "$f")
echo "$out"
if echo "$out" | grep -q "far=0 "; then ../bin/apsp "$f" 3 7 | tail -1; fi
