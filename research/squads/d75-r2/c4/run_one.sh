#!/bin/bash
# run_one.sh GROUP ALPHA F M : tabu search for SECS seconds, writes logs/sweep/ and edges/ for the first solution
cd /home/user/degree-diameter/research/squads/d75-r2/c4
export TMPDIR=$PWD/tmp
g=$1; a=$2; f=$3; m=$4
tag="${g}_a${a}_f${f}m${m}"
EDGES=$PWD/edges/$tag.edges SECS=${SECS:-10} SEED=${SEED:-1} MODE=tabu nice -n 15 timeout 120 ./anneal g$g.ht $a $f $m > logs/sweep/$tag.out 2>&1
echo "$tag $(grep -c '^SOL' logs/sweep/$tag.out) $(grep '^END' logs/sweep/$tag.out | head -1)"
