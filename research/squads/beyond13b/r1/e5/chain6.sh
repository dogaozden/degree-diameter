#!/bin/bash
# Record push and knob comparison (each run stops at cost 0; wall budget 480 s).
# 1: ORBIT "5 1 1" psl 89 x Z_61 (2N 42997680), defaults.   2: same group, knobs K=32 TARGP=95 REHEATSTEPS=15 COOLSTEPS=1.
# 3: ORBIT "5 1 1" sl 89 x Z_31 (2N 43702560), defaults.
B=/home/user/degree-diameter/research/frontier/beyond13/bin
cd /home/user/degree-diameter/research/squads/beyond13b/r1/e5
echo "R1 start $(date -u +%T)"
ORBIT="5 1 1" $B/haar_big0 6 13 480 31 8 out/r1.sol psl 89 61 >out/r1.out 2>out/r1.err; grep 'RESULT\|re-eval' out/r1.out
echo "R2 start $(date -u +%T)"
ORBIT="5 1 1" TARGP=95 REHEATSTEPS=15 COOLSTEPS=1 $B/haar_big0 6 13 480 32 32 out/r2.sol psl 89 61 >out/r2.out 2>out/r2.err; grep 'RESULT\|re-eval' out/r2.out
echo "R3 start $(date -u +%T)"
ORBIT="5 1 1" $B/haar_big0 6 13 480 33 8 out/r3.sol sl 89 31 >out/r3.out 2>out/r3.err; grep 'RESULT\|re-eval' out/r3.out
echo "CHAIN6 DONE $(date -u +%T)"
