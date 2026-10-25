#!/bin/bash
# A8 wrapper, runs inside ONE gate slot: (1) plain (unsymmetric) anneal, no ORBIT; (2) AR=1 screen of the k=5 Frobenius family.
A8=/home/user/degree-diameter/research/squads/d11D10-r2/A8
H=/home/user/degree-diameter/research/structured/haar_sym
cd "$A8" || exit 1
echo "start $(date -u +%T)"
env -u THREADS $H 11 10 240 1 8 "$A8/d11D10_psl_243_11_plain_s1.txt" psl 243 11 > "$A8/plain_s1.log" 2>&1
echo "plain rc=$? end $(date -u +%T)"
env -u THREADS ORBIT="5 2 1" AFROB=1 AR=1 RANDORB=16 $H 11 10 60 1 8 /dev/null psl 243 11 > "$A8/ar1_screen.log" 2>&1
echo "ar1 rc=$? end $(date -u +%T)"
