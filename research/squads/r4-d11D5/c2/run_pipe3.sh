#!/bin/bash
# card c2: fresh po7 anneal (T0=8, T1=0.3, SECS=600) from the start-20 state; wpo only if the best cost is <= 20.
cd /home/user/degree-diameter/research/squads/r4-d11D5/c2
timeout 1500 nice -n 10 env THREADS=1 SECS=600 T0=8 T1=0.3 OUT=sa_f20.in OUT0=fail0_n587_sa_f20.in ./po7 start_20.in > log_sa_f20.txt 2>&1
c=$(grep RESULT log_sa_f20.txt | sed -E 's/.*best=([0-9]+).*/\1/')
echo "po7 fresh T0=8 best=$c $(date +%T)"
if grep -q FAIL0 log_sa_f20.txt; then cp fail0_n587_sa_f20.in fail0_n587.in; echo "FAIL0 in po7"; echo ALLDONE3; exit 0; fi
if [ "$c" -le 20 ]; then
  timeout 1500 nice -n 10 env THREADS=1 SECS=600 SEED=1 OUT=out_f20.in OUT0=fail0_n587_f20.in ./wpo sa_f20.in > log_wpo_f20.txt 2>&1
  echo "wpo done $(date +%T)"
  if grep -q FAIL0 log_wpo_f20.txt; then cp fail0_n587_f20.in fail0_n587.in; echo "FAIL0 in wpo"; fi
else
  echo "cost above 20, wpo not started"
fi
echo ALLDONE3
