#!/bin/bash
# c11: haar_sym ORBIT "3 1 1" (d=4: S = {e, x, a x, a^2 x}, a = conj of order 3 times z -> r z) over psl/sl/pgl x Z_n
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r1/c11
# 1. screen every candidate (N in 1094..1400) with 20000 random symmetric S (the family has only ~N/3 members)
while read -r fam q n; do THREADS=1 ORBIT="3 1 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 4 8 10 1 8 /dev/null $fam $q $n 2>&1 | grep "^RANDORB d="; done < cands.txt > screen20k.txt
# 2. both order-3 scalings on the cyclic factor, and the calibration psl 13 (N = 1092)
for spec in "psl 5 19 7" "psl 5 19 11" "psl 7 7 2" "psl 7 7 4" "pgl 3 49 18" "pgl 3 49 30" "sl 3 49 18" "sl 3 49 30"; do set -- $spec; r=$4; set -- $1 $2 $3; THREADS=1 AR=$r ORBIT="3 1 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 4 8 10 1 8 /dev/null $1 $2 $3 2>&1 | grep -E "^alpha|RANDORB d="; done > scan_AR.txt
# 3. best candidate, exhaustive-style count (best of the whole family)
THREADS=1 ORBIT="3 1 1" RANDORB=60000 timeout 120 nice -n 10 $B/haar_sym 4 8 10 1 8 /dev/null psl 7 7
