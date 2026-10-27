#!/bin/bash
# run_glp.sh K: glift (independent of zplift) over the cyclic groups of prime order p >= 11 with 170 <= 2kp <= 248.
cd "$(dirname "$0")/../.."
S=/tmp/claude-0/-home-user-degree-diameter/12d74605-d8e1-550d-b7fb-3e2ad7b58b29/scratchpad/bases
B=bases/b$1.txt; [ -f $B ] || B=$S/b$1.txt
t0=$(date +%s); nice -n 15 ./bin/glift_fix groups/p$1.txt 7 < $B > runs/gl/glp_k$1.out; t1=$(date +%s)
echo "k=$1 runs=$(grep -c '^RES' runs/gl/glp_k$1.out) searched=$(grep '^RES' runs/gl/glp_k$1.out | grep -vc skip) nodes=$(sed -n 's/.*nodes=\([0-9]*\).*/\1/p' runs/gl/glp_k$1.out | awk '{s+=$1} END{print s+0}') sols=$(grep -c '^SOL' runs/gl/glp_k$1.out) time=$((t1-t0))s" >> runs/gl/summary_prime.log
