#!/bin/bash
# sequential q=13 checks: wait for the running q=7 continuation, then k=2 full check and k=3 anneal (NSRC sampled)
cd /home/user/degree-diameter/research/squads/d16D8-r2/c2
B=../../../d16D8/baselift
while pgrep -f "anneal t7_k4_B_c1.base" >/dev/null; do sleep 2; done
echo "== q7 k4 continuation:"; $B eval t7_k4_B_c2.base 6
python3 -B build.py 13 2 1 B t13_k2_B.base
echo "== q13 k2 random skeleton, full check:"; $B eval t13_k2_B.base 6
echo "== q13 k3 anneal (NSRC=200, 150 s):"
FIXMOD=5 MOVES=vvvM T0=2 T1=0.1 NSRC=200 timeout 900 nice -n 10 $B anneal t13_k3_B.base 6 150 3 t13_k3_B_out.base 2>&1 | tail -1
echo "== q13 k3 full check:"; $B eval t13_k3_B_out.base 6
echo CHAIN1_DONE
