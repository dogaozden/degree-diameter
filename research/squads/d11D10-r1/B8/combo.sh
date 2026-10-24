#!/bin/bash
# B8 combined screen (one gate slot): metacyclic Z_p x|_r Z_c, ORBIT "5 2 1" with the automatic meta scaling alpha.
# c = 5 is the main candidate (fix = 5, N = 71,118,455): 200 random S, a cost-0 S is written and checked.
# Then the k = 3 calibration psl 149 x Z43 (ORBIT "3 3 2"), and c = 10 for comparison.
H=/home/user/degree-diameter/research/structured/haar_sym
D=/home/user/degree-diameter/research/squads/d11D10-r1/B8
unset THREADS
cd "$D" || exit 1
OUT5="$D/d11D10_meta_14223691_5_orb5_B8_s1.txt"
echo "=== meta p=14223691 c=5 r=3428689 (N=71118455), RANDORB=200"
env ORBIT="5 2 1" RANDORB=200 "$H" 11 10 1 1 8 "$OUT5" meta 14223691 5 3428689 1
echo "rc=$?"
if [ -s "$OUT5" ]; then echo "=== metacheck $OUT5"; "$D/metacheck" "$OUT5"; echo "metacheck rc=$?"; fi
echo "=== baseline psl 149 x Z43, ORBIT 3 3 2, RANDORB=60"
env ORBIT="3 3 2" RANDORB=60 "$H" 11 10 1 1 8 /dev/null psl 149 43
echo "rc=$?"
echo "=== meta p=7111771 c=10 r=2862052 (N=71117710), RANDORB=20"
env ORBIT="5 2 1" RANDORB=20 "$H" 11 10 1 1 8 /dev/null meta 7111771 10 2862052 1
echo "rc=$?"
