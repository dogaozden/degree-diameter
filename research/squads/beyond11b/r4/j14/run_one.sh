#!/bin/bash
# usage: run_one.sh RUNID SEED K START_FILE_OR_DASH
J=/home/user/degree-diameter/research/squads/beyond11b/r4/j14
ID=$1; SEED=$2; K=$3; ST=$4
cd $J
if [ "$ST" = "-" ]; then STENV=""; else STENV="START=$J/$ST"; fi
env THREADS=1 $STENV SAVEBEST=$J/best_$ID.txt timeout 105 nice -n 10 $J/hg3s 5 11 95 $SEED $K $J/sol_$ID.txt meta 8209 19 477 1 > $J/out_$ID.log 2> $J/err_$ID.log
RC=$?
START_COST=$(grep -o 'start cost=[0-9]*' $J/err_$ID.log | head -1)
BEST=$(grep -o 'RESULT.*' $J/out_$ID.log | grep -o 'best=[0-9]*' | head -1)
EVALS=$(grep -o 'evals=[0-9]*' $J/out_$ID.log | head -1)
echo "run=$ID seed=$SEED K=$K start_from=$ST rc=$RC $START_COST $BEST $EVALS saved=$(head -1 $J/best_$ID.txt 2>/dev/null | grep -o 'cost [0-9]*')" | tee -a $J/runs.txt
