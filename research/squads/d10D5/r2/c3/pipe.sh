#!/bin/bash
# pipe.sh NAME FLAGLS_OUT [SEED]: flags+sigma (flagls2 output) -> coverage repair -> coset-0 -> hub graph -> exact APSP
set -u
N=$1; SRC=$2; SD=${3:-1}
cd "$(dirname "$0")"
python3 write_partial.py "$SRC" "$N.sol" || exit 1
FREE="$(cat $N.sol.free)"
echo "== coverage repair (dmhub COVIT)"
FREE="$FREE" COVIT=3000000 CT0=0.25 ITERS=0 NOHUBG=1 SEED=$SD timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin "$N.sol" "a_$N" | grep -E 'cover cost'
python3 sol2lift2.py "a_$N.sol" "a_${N}_l2.sol" > /dev/null
echo "== coset-0 (dmfast_hub RELAX PATCH PTARG)"
FREE="$FREE" RELAX=1 PATCH=1 PTARG=0.5 IN="a_${N}_l2.sol" OUT="b_$N.sol" BASE=gq/gq_q7.bin NPOLY=4 ITERS=3000000 TEMP0=0.25 TEMP1=0.02 SWAPP=0.01 SEED=$SD timeout 900 nice -n 10 ./dmfast_hub 7 2>&1 | tail -2
echo "== hub graph + exact cost (dmhub HGIT)"
FREE="$FREE" ITERS=0 HGIT=3000000 SEED=$SD timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin "b_$N.sol" "final_$N" | grep -E 'final cost|hub graph'
echo "== APSP"
./apsp "final_$N.edges" 10 5
