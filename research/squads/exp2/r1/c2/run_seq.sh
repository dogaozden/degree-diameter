#!/bin/bash
# card c2, exp2 squad round 1: random sparse hub graphs (gen_hg.py K 2 4), d7hex mode 3, alg 2, seed 2.
# K = 18, 24, 32 with mind 4, stopping at the first unsolved K; then mind 6 on that K; then score the largest solved K.
cd /home/user/degree-diameter/research/squads/exp2/r1/c2 || exit 1
SEED=2
: > seq.log
: > solved.txt
run() {  # run K MIND
  local K=$1 MIND=$2 t0 t1 rc res
  t0=$(date +%s)
  timeout 900 nice -n 10 ./d7hex search hex/hex_q5.bin 0 $SEED 400 k${K}_m${MIND}.sol 3 2 $MIND hg${K}.hg > run_k${K}_m${MIND}.log 2>&1
  rc=$?
  t1=$(date +%s)
  res=$(grep '^RESULT' run_k${K}_m${MIND}.log | tail -1)
  echo "K=$K mind=$MIND seed=$SEED rc=$rc wall=$((t1-t0))s :: ${res:-NO RESULT LINE}" >> seq.log
  if echo "$res" | grep -q ' VALID$'; then echo "$K $MIND" >> solved.txt; return 0; fi
  return 1
}
FAILED=""
for K in 18 24 32; do
  if ! run $K 4; then FAILED=$K; break; fi
done
if [ -n "$FAILED" ]; then run $FAILED 6; fi
echo "search finished" >> seq.log
BEST=$(sort -n solved.txt | tail -1)
if [ -n "$BEST" ]; then
  set -- $BEST
  K=$1; MIND=$2; SOL=k${K}_m${MIND}.sol
  ./d7hex edges hex/hex_q5.bin $SOL e_best.txt > edges.err 2>&1
  timeout 900 nice -n 10 ./apsp e_best.txt 7 7 > apsp_best.txt 2>&1
  echo "scored K=$K mind=$MIND sol=$SOL :: $(grep RESULT apsp_best.txt) | $(head -1 apsp_best.txt)" >> seq.log
fi
echo "ALL DONE" >> seq.log
