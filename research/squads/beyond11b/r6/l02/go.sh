#!/bin/bash
# usage: go.sh NAME BIN SEED K START SECS [ENV=VAL ...]   (meta 74719 63 37726, n=1, d=6 D=12)
D=/home/user/degree-diameter/research/squads/beyond11b/r6/l02
B=/home/user/degree-diameter/research/squads/beyond11b/bin
name=$1; bin=$2; seed=$3; K=$4; start=$5; secs=$6; shift 6
cd "$D" || exit 1
env START="$start" SAVEBEST="$D/$name.best" THREADS=1 "$@" timeout 105 nice -n 10 "$B/$bin" 6 12 "$secs" "$seed" "$K" "$D/$name.sol" meta 74719 63 37726 1 > "$D/$name.log" 2>&1
res=$(grep RESULT "$D/$name.log")
[ -f "$D/$name.sol" ] && sol=sol || sol=nosol
echo "$name bin=$bin seed=$seed K=$K start=$(basename $start) env=[$*] secs=$secs | $res | $sol" >> "$D/runs.txt"
echo "$name: $res $sol"; tail -2 "$D/$name.log" | head -1
