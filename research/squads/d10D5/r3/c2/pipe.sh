#!/bin/bash
# pipe.sh X : after dmhub reached cover cost 0 in X.sol: lift2 conversion, coset-0 (dmfast_hub), dmhub on it, apsp.
# run from the card folder; one heavy process at a time (the commands run sequentially).
set -u
X=$1
FREESTR=$(grep '^free' $X.sol | cut -d' ' -f2-)
python3 sol2lift2.py $X.sol ${X}_l2.sol > /dev/null
eval $(python3 mkhubadj.py $X.sol)
echo "FREE=$FREESTR"
FREE="$FREESTR" RELAX=1 HUBADJ="$HUBADJ" PTARG=0.5 SWAPP=0.01 ITERS=30000000 TEMP0=0.25 TEMP1=0.02 SEED=1 THREADS=1 \
  IN=${X}_l2.sol OUT=${X}_c0.sol BASE=gq/gq_q7.bin NPOLY=4 timeout 900 nice -n 10 ./dmfast_hub 7 > ${X}_c0.log 2>&1
tail -3 ${X}_c0.log
head -1 ${X}_c0.sol
FREE="$FREESTR" HUBG_IN=$X.sol ITERS=0 THREADS=1 timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin ${X}_c0.sol ${X}_out > ${X}_out.log 2>&1
tail -2 ${X}_out.log
timeout 900 nice -n 10 ./apsp ${X}_out.edges 10 5 | tail -2
