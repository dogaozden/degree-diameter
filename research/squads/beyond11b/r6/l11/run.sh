#!/bin/bash
# usage: run.sh NAME SEED K START|- TFULL(0/1) BIN(haar_gen3|haar_gen3t) SPEC...   (d=6 D=12, 90 s, THREADS=1)
L=/home/user/degree-diameter/research/squads/beyond11b/r6/l11
B=/home/user/degree-diameter/research/squads/beyond11b/bin
name=$1; seed=$2; K=$3; start=$4; tf=$5; bin=$6; shift 6
cd "$L" || exit 1
envs="SAVEBEST=$L/$name.best THREADS=1 TFULL=$tf TARGP=100"
[ "$start" != "-" ] && envs="$envs START=$start"
env $envs timeout 105 nice -n 10 "$B/$bin" 6 12 90 "$seed" "$K" "$L/$name.sol" "$@" 1 > "$L/$name.log" 2>&1
res=$(grep RESULT "$L/$name.log")
[ -f "$L/$name.sol" ] && sol=sol || sol=nosol
echo "$name seed=$seed K=$K start=$start tfull=$tf bin=$bin spec=$* | $res | $sol" >> "$L/runs.txt"
echo "$name: $res $sol"
