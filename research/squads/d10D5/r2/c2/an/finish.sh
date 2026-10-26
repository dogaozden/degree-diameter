#!/bin/bash
# usage: finish.sh P L L2FILE TAG  -> coset-0 relaxed anneal (dmfast_hub), then hub graph + exact BFS (dmhub), then apsp
cd /home/user/degree-diameter/research/squads/d10D5/r2/c2
F0="266 41 225 65 263 283 398 253"; P=$1; L2=$2; TAG=$3; FR="$F0 $P"
s=$(date +%s)
FREE="$FR" RELAX=1 PATCH=1 PTARG=1.0 TEMP0=0.5 TEMP1=0.05 SWAPP=0.05 ITERS=3000000 SEED=1 IN=$L2 OUT=${TAG}_b.sol BASE=gq/gq_q7.bin NPOLY=4 timeout 600 nice -n 10 ./dmfast_hub 7 > log_${TAG}_coset0.txt 2>&1
e=$(date +%s); echo "coset0 done in $((e-s))s: $(grep -E 'relaxed|RESULT' log_${TAG}_coset0.txt | tr '\n' ' ')"
FREE="$FR" ITERS=0 HGIT=3000000 timeout 600 nice -n 10 ./dmhub gq/gq_q7.bin ${TAG}_b.sol ${TAG}_final > log_${TAG}_hub.txt 2>&1
f=$(date +%s); echo "hub done in $((f-e))s: $(grep -E 'coverage holes|hub graph|final cost' log_${TAG}_hub.txt | tr '\n' ' ')"
if [ -f ${TAG}_final.edges ]; then timeout 300 nice -n 10 ./apsp ${TAG}_final.edges 10 5 | tail -1; fi
echo FINISHED
