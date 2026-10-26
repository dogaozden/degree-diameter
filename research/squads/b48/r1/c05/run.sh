#!/bin/bash
# card c05: prime k >= 5 metacyclic Haar graphs, N = m*k in 1094..1250 (candidates from enum.py)
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
D=/home/user/degree-diameter/research/squads/b48/r1/c05
cd $D
python3 cands_enum.py > cands.txt
while read N m p r; do echo -n "$N $m $p $r :: "; THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 8 1 8 s1_${N}_${m}_${p}_${r}.txt meta $m $p $r 1 2>&1 | grep RESULT; done < cands.txt > screen8.txt
for c in "1204 172 7 21" "1220 244 5 9" "1210 242 5 3"; do set -- $c; echo -n "$1 $2 $3 $4 :: "; THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 40 2 8 l40_$1_$2_$3_$4.txt meta $2 $3 $4 1 2>&1 | grep RESULT; done > long40.txt
