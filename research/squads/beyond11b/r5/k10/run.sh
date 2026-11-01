#!/bin/bash
# usage: run.sh NAME SEED K START|- SPEC...   (d=6 D=12, 95 s, THREADS=1, saves best state to NAME.best)
D=/home/user/degree-diameter/research/squads/beyond11b/r5/k10
B=/home/user/degree-diameter/research/squads/beyond11b/bin
name=$1; seed=$2; K=$3; start=$4; shift 4
cd "$D" || exit 1
if [ "$start" = "-" ]; then
  env SAVEBEST="$D/$name.best" THREADS=1 timeout 105 nice -n 10 "$B/haar_gen3s" 6 12 95 "$seed" "$K" "$D/$name.sol" "$@" 1 > "$D/$name.log" 2>&1
else
  env START="$start" SAVEBEST="$D/$name.best" THREADS=1 timeout 105 nice -n 10 "$B/haar_gen3s" 6 12 95 "$seed" "$K" "$D/$name.sol" "$@" 1 > "$D/$name.log" 2>&1
fi
res=$(grep RESULT "$D/$name.log")
[ -f "$D/$name.sol" ] && sol=sol || sol=nosol
echo "$name seed=$seed K=$K start=$start spec=$* | $res | $sol" >> "$D/runs.txt"
echo "$name: $res $sol"
