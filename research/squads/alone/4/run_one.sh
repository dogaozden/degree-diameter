#!/bin/bash
# usage: run_one.sh NAME ORDER SECONDS SEED  GROUP-ARGS...   (d=16 D=5, appends scoreboard line)
D=/home/user/degree-diameter/research/squads/alone/4
name=$1; order=$2; secs=$3; seed=$4; shift 4
out=$D/runs/$name.txt
THREADS=1 $D/haar_gen3 16 5 $secs $seed 20 $out "$@" > $D/runs/$name.log 2>&1
res=$(grep RESULT $D/runs/$name.log)
best=$(echo "$res" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
valid=false; score=$best
if [ "$best" = "0" ]; then valid=true; score=$((2*order)); fi
echo "{\"idea\": \"prod-family direct product $name, D=5 d=16, annealing ${secs}s\", \"command\": \"THREADS=1 haar_gen3 16 5 $secs $seed 20 runs/$name.txt $*\", \"score\": ${score:-null}, \"valid\": $valid}" >> $D/scoreboard.tmp
