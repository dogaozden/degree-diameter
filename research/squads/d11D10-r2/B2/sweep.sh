#!/bin/bash
# B2 sweep: all runs back to back inside one gate slot (same machine state for the A/B comparisons).
B=/home/user/degree-diameter/research/squads/d11D10-r2/B2
H=/home/user/degree-diameter/research/structured/haar_sym
cd "$B" || exit 1
echo "START $(date +%T)"
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 ORBPROF=1 SEQ=1 PFDLIST="8 0 4 16 32" FAST=2 \
  "$B/haar_sym_B2" 11 10 600 5 8 /dev/null psl 243 11 > "$B/p1_fast2_pfd.log" 2>&1; echo "P1 rc=$? $(date +%T)"
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 ORBPROF=1 SEQ=1 PFDLIST="8 16" HUGEPG=1 FAST=2 \
  "$B/haar_sym_B2" 11 10 600 5 8 /dev/null psl 243 11 > "$B/p3_hugepg.log" 2>&1; echo "P3 rc=$? $(date +%T)"
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 ORBPROF=1 SEQ=1 FAST=1 \
  "$B/haar_sym_B2" 11 10 600 5 8 /dev/null psl 243 11 > "$B/p2_fast1.log" 2>&1; echo "P2 rc=$? $(date +%T)"
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=30 FAST=2 \
  "$H" 11 10 600 5 8 /dev/null psl 243 11 > "$B/p4_original.log" 2>&1; echo "P4 rc=$? $(date +%T)"
echo "SWEEP_DONE $(date +%T)"
