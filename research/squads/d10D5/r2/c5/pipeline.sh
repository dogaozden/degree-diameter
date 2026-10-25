#!/bin/bash
# pipeline.sh TAG "p:l p:l ..."   (run in the card folder; one heavy process at a time)
# relaxsol.py (max exact matching, rest completed arbitrarily) -> dmhub COVIT coverage (must reach 0) -> lift2 ->
# dmfast_hub coset-0 (RELAX PATCH PTARG) -> dmhub hub graph + exact BFS cost -> apsp (SCORER line).
set -u
T=$1; FLAGS=$2
SOL0=../../../../d10D7/graphs/d10D5_n4800_gqdm_q7.sol
python3 -I relaxsol.py gq/gq_q7.bin "$FLAGS" $SOL0 $T || { echo "PIPE $T relaxsol FAILED"; exit 1; }
FR="$(cat $T.sol.free)"
echo "== coverage"; FREE="$FR" COVIT=${COVIT0:-3000000} CT0=0.25 ITERS=0 NOHUBG=1 timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin $T.sol ${T}a > ${T}a.log 2>&1
grep -E "cover cost|final cost" ${T}a.log
grep -q "cover cost final 0$" ${T}a.log || { echo "PIPE $T COVER NOT ZERO"; exit 2; }
python3 sol2lift2.py ${T}a.sol ${T}a_l2.sol > /dev/null
echo "== coset-0"; FREE="$FR" RELAX=1 PATCH=1 PTARG=0.5 IN=${T}a_l2.sol OUT=${T}b.sol BASE=gq/gq_q7.bin NPOLY=4 ITERS=${ITERS0:-30000000} TEMP0=${TEMP00:-0.25} TEMP1=${TEMP10:-0.02} SWAPP=${SWAPP0:-0.01} SEED=${SEED0:-1} timeout 900 nice -n 10 ./dmfast_hub 7 > ${T}b.log 2>&1
grep -E "RESULT" ${T}b.log
echo "== hub graph"; FREE="$FR" ITERS=0 HGIT=3000000 timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin ${T}b.sol ${T}final > ${T}final.log 2>&1
grep -E "coverage holes|hub graph|hub src|final cost" ${T}final.log
echo "== apsp"; timeout 900 nice -n 10 ./apsp ${T}final.edges 10 5 | tail -2
