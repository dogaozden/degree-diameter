#!/bin/bash
# usage: run.sh RUNID SEED K START_FILE_OR_DASH
B=/home/user/degree-diameter/research/squads/beyond11b/bin
J=/home/user/degree-diameter/research/squads/beyond11b/r5/k09
ID=$1; SEED=$2; K=$3; ST=$4; T0=$(date +%s)
cd $J
if [ "$ST" = "-" ]; then STENV=""; else STENV="START=$J/$ST"; fi
env THREADS=1 $STENV SAVEBEST=$J/best_$ID.txt timeout 105 nice -n 10 $B/haar_gen3s 6 12 ${SECS:-40} $SEED $K $J/sol_$ID.txt meta 74719 63 37726 1 > $J/out_$ID.log 2> $J/err_$ID.log
RC=$?
START_COST=$(grep -o 'start cost=[0-9]*' $J/err_$ID.log | head -1)
BEST=$(grep -o 'RESULT.*' $J/out_$ID.log | grep -o 'best=[0-9]*' | head -1)
EVALS=$(grep -o 'evals=[0-9]*' $J/out_$ID.log | head -1)
echo "wall=$(( $(date +%s) - T0 )) run=$ID seed=$SEED K=$K start_from=$ST rc=$RC $START_COST $BEST $EVALS saved=$(head -1 $J/best_$ID.txt 2>/dev/null | grep -o 'cost [0-9]*') sol=$(ls $J/sol_$ID.txt 2>/dev/null)" | tee -a $J/runs.txt
