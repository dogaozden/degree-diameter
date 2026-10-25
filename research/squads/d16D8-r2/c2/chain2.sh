#!/bin/bash
# q=7 k=2 and k=3 variant B anneals (full cost), then q=13 k=2 anneal (NSRC=300 sampled), full checks
cd /home/user/degree-diameter/research/squads/d16D8-r2/c2
B=../../../d16D8/baselift
echo "== q7 k2 B anneal 60 s:"
FIXMOD=5 MOVES=vvvM T0=2 T1=0.1 timeout 900 nice -n 10 $B anneal t7_k2_B_rnd.base 6 60 5 t7_k2_B_out.base 2>/dev/null | tail -1
$B eval t7_k2_B_out.base 6
echo "== q13 k2 B anneal 150 s (NSRC=300):"
FIXMOD=5 MOVES=vvvM T0=2 T1=0.1 NSRC=300 timeout 900 nice -n 10 $B anneal t13_k2_B.base 6 150 6 t13_k2_B_out.base 2>/dev/null | tail -1
echo "== q13 k2 full check:"; $B eval t13_k2_B_out.base 6
echo "== q7 k3 B anneal 60 s:"
FIXMOD=5 MOVES=vvvM T0=2 T1=0.1 timeout 900 nice -n 10 $B anneal t7_k3_B_rnd.base 6 60 7 t7_k3_B_out.base 2>/dev/null | tail -1
$B eval t7_k3_B_out.base 6
echo CHAIN2_DONE
