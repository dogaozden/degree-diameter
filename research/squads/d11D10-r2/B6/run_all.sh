#!/bin/bash
# B6 job (runs inside ONE gate slot): compile the B6 copy, a smoke test, the uniform 150-sample run, the stratified run.
B=/home/user/degree-diameter/research/squads/d11D10-r2/B6
H=$B/haar_sym_B6
COMMON='ORBIT=10 1 1 AFROB=1 AFROBH=0 1 2 0 AR=2'
cd "$B" || exit 1
gcc -O3 -march=native -fopenmp -Wall -o "$H" "$B/haar_sym_B6.c" -lm > "$B/build.log" 2>&1 || { echo "BUILD FAILED $(date -u +%T)"; exit 1; }
echo "built $(date -u +%T)"
env $COMMON B6STRAT="2,121,0" RANDORB=6 "$H" 11 10 60 6 8 /dev/null psl 243 11 > "$B/smoke.log" 2>&1
echo "smoke rc=$? $(date -u +%T)"
env $COMMON RANDORB=150 "$H" 11 10 60 6 8 /dev/null psl 243 11 > "$B/run_uniform.log" 2>&1
echo "uniform rc=$? $(date -u +%T)"
env $COMMON B6STRAT="2,3,11,61,121,122,0" RANDORB=140 "$H" 11 10 60 6 8 /dev/null psl 243 11 > "$B/run_strat.log" 2>&1
echo "strat rc=$? $(date -u +%T)"
