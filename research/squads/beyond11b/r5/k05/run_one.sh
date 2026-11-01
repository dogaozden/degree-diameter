#!/bin/bash
# usage: run_one.sh RUNID SEED K START_FILE_OR_DASH
B=/home/user/degree-diameter/research/squads/beyond11b/bin
W=/home/user/degree-diameter/research/squads/beyond11b/r5/k05
ID=$1; SEED=$2; K=$3; ST=$4
cd $W
if [ "$ST" = "-" ]; then STENV=""; else STENV="START=$W/$ST"; fi
env THREADS=1 $STENV SAVEBEST=$W/best_$ID.txt timeout 105 nice -n 10 $B/haar_gen3s 5 11 95 $SEED $K $W/sol_$ID.txt meta 5023 31 2886 1 > $W/out_$ID.log 2> $W/err_$ID.log
RC=$?
START_COST=$(grep -o 'start cost=[0-9]*' $W/err_$ID.log $W/out_$ID.log | head -1)
BEST=$(grep -o 'RESULT.*' $W/out_$ID.log | grep -o 'best=[0-9]*' | head -1)
EVALS=$(grep -o 'evals=[0-9]*' $W/out_$ID.log | tail -1)
SOL=$(ls $W/sol_$ID.txt 2>/dev/null)
echo "run=$ID seed=$SEED K=$K start_from=$ST rc=$RC $START_COST $BEST $EVALS saved=$(head -1 $W/best_$ID.txt 2>/dev/null | cut -c1-60) sol=${SOL:-none} $(date +%H:%M:%S)" | tee -a $W/runs.txt
