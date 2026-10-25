#!/bin/bash
# pipe2.sh NAME SOL FREE [SEED]: lift2 sol + .free -> coverage check -> coset-0 (PTARG) -> hub graph -> APSP
set -u
N=$1; SOLF=$2; FRF=$3; SD=${4:-1}
cd "$(dirname "$0")"
FREE="$(cat $FRF)"
echo "== coverage check (dmhub COVIT)"
FREE="$FREE" COVIT=3000000 CT0=0.25 ITERS=0 NOHUBG=1 SEED=$SD timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin "$SOLF" "a_$N" | grep -E 'cover cost'
python3 sol2lift2.py "a_$N.sol" "a_${N}_l2.sol" > /dev/null
echo "== coset-0 (dmfast_hub RELAX PATCH PTARG)"
FREE="$FREE" RELAX=1 PATCH=1 PTARG=0.5 IN="a_${N}_l2.sol" OUT="b_$N.sol" BASE=gq/gq_q7.bin NPOLY=4 ITERS=3000000 TEMP0=0.25 TEMP1=0.02 SWAPP=0.01 SEED=$SD timeout 900 nice -n 10 ./dmfast_hub 7 2>&1 | tail -2
echo "== hub graph + exact cost (dmhub HGIT)"
FREE="$FREE" ITERS=0 HGIT=3000000 SEED=$SD timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin "b_$N.sol" "final_$N" | grep -E 'final cost|hub graph'
echo "== APSP"
./apsp "final_$N.edges" 10 5
