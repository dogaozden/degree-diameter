#!/bin/bash
# One larger check (about 0.5M vertices): haar_sym solution over PSL(2,49) x Z_4, then both checkers.
B=/home/user/degree-diameter/research/squads/d11D10-r1/B2
H=/home/user/degree-diameter/research/structured/haar_sym
F=/home/user/degree-diameter/research/frontier/build_haar2.py
cd $B
timeout 200 $H 11 10 60 4 8 d11D10_psl_49_4_orb1_B2big_s4.txt psl 49 4 > run_big.log 2>&1
f=d11D10_psl_49_4_orb1_B2big_s4.txt
[ -s "$f" ] || { echo "no solution file" >> b2_big.progress; exit 0; }
s=$(date +%s); timeout 300 ./haarcheck_pq "$f" > big.pq.out 2>&1; echo "pq rc=$? secs=$(( $(date +%s) - s ))" >> b2_big.progress
s=$(date +%s); timeout 900 python3 "$F" "$f" > big.b2.out 2>&1; echo "b2 rc=$? secs=$(( $(date +%s) - s ))" >> b2_big.progress
echo B2_BIG_DONE >> b2_big.progress
