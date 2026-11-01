#!/bin/bash
# usage: [env: START SAVEBEST TFULL TMAX TARGP] ./run.sh NAME SECS SEED K SPEC...  (haar_gen3t, d=4 D=11, n=1)
cd /home/user/degree-diameter/research/squads/beyond11b/r6/l10
B=/home/user/degree-diameter/research/squads/beyond11b/bin
name=$1; secs=$2; seed=$3; K=$4; shift 4
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3t 4 11 $secs $seed $K $name.sol "$@" 1 > log_$name.txt 2>&1
res=$(grep RESULT log_$name.txt | sed 's/.*best=/best=/')
ev=$(env | grep -E '^(START|SAVEBEST|TFULL|TMAX|TARGP)=' | tr '\n' ' ')
echo "$name seed=$seed K=$K $ev spec=[$*] $res $(date +%H:%M:%S)" >> runs.txt
echo "$name $res $(grep -c . log_$name.txt) lines; $(ls $name.sol 2>/dev/null)"
