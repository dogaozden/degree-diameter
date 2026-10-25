#!/bin/bash
# Card B5 (round d11D10-r2): ball-growth census on psl 243 x Z11, RANDORB=4 LEVELS=4, three families.
# Runs inside ONE gate slot: gate.sh 480 bash .../B5/run_census.sh
# Each haar_sym run prints the per-sample BFS levels on stderr ("levels: lev0 ... lev8 cost c").
unset THREADS
export OMP_NUM_THREADS=1
cd /home/user/degree-diameter/research/squads/d11D10-r2/B5 || exit 1
H=/home/user/degree-diameter/research/structured/haar_sym
echo "start $(date +%T)"
ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=4 LEVELS=4 timeout 200 "$H" 11 10 60 1 8 /dev/null psl 243 11 > k10_afrobh.out 2> k10_afrobh.err
echo "k10_afrobh rc=$? $(date +%T)"
ORBIT="10 1 1" AFROB=1 AFROBD=1 AR=2 RANDORB=4 LEVELS=4 timeout 200 "$H" 11 10 60 1 8 /dev/null psl 243 11 > k10_afrobd.out 2> k10_afrobd.err
echo "k10_afrobd rc=$? $(date +%T)"
ORBIT="5 2 1" AFROB=3 RANDORB=4 LEVELS=4 timeout 200 "$H" 11 10 60 1 8 /dev/null psl 243 11 > k5_afrob3.out 2> k5_afrob3.err
echo "k5_afrob3 rc=$? $(date +%T)"
echo "end $(date +%T)"
