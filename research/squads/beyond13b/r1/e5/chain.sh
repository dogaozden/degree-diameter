#!/bin/bash
# Stage 1: k=3 control RANDORB on the shape the k=5 screen picked (psl 101 x Z_41).
# Stage 2: anneal ORBIT "5 1 1" on psl 101 x Z_41, defaults (K=8), 600 s.
# Stage 3: same, knobs K=32 TARGP=95 REHEATSTEPS=15 COOLSTEPS=1, 600 s.
# Stage 4: control anneal ORBIT "3 2 0" on the same group, defaults, 600 s.
B=/home/user/degree-diameter/research/frontier/beyond13/bin
cd /home/user/degree-diameter/research/squads/beyond13b/r1/e5
ORBIT="3 2 0" RANDORB=60 $B/haar_big0 6 13 1 1 8 out/scr_320_psl_101_41.sol psl 101 41 2>>out/screen.err | grep '^RANDORB d' | sed 's/^/k=3 /'
echo "A start $(date -u +%T)"
ORBIT="5 1 1" $B/haar_big0 6 13 600 11 8 out/anA.sol psl 101 41 >out/anA.out 2>out/anA.err; grep RESULT out/anA.out; grep 'cost 0\|re-eval' out/anA.out
echo "B start $(date -u +%T)"
ORBIT="5 1 1" TARGP=95 REHEATSTEPS=15 COOLSTEPS=1 $B/haar_big0 6 13 600 12 32 out/anB.sol psl 101 41 >out/anB.out 2>out/anB.err; grep RESULT out/anB.out; grep 'cost 0\|re-eval' out/anB.out
echo "C start $(date -u +%T)"
ORBIT="3 2 0" $B/haar_big0 6 13 600 13 8 out/anC.sol psl 101 41 >out/anC.out 2>out/anC.err; grep RESULT out/anC.out; grep 'cost 0\|re-eval' out/anC.out
echo "CHAIN DONE $(date -u +%T)"
