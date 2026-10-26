#!/bin/bash
# card c2 of round r4-d11D5: three best n = 587 starts (inc8 switches, seeds 20, 17, 23): SA (po7) then wpo.
cd /home/user/degree-diameter/research/squads/r4-d11D5/c2
for s in 20 17 23; do
  cp cand/inc8_$s.in start_$s.in
  timeout 1500 nice -n 10 env THREADS=1 SECS=200 T0=3 T1=0.3 OUT=sa_$s.in OUT0=fail0_n587_sa$s.in ./po7 start_$s.in > log_sa_$s.txt 2>&1
  echo "sa $s done $(date +%T)"
  timeout 1500 nice -n 10 env THREADS=1 SECS=600 SEED=1 OUT=out_$s.in OUT0=fail0_n587_s$s.in ./wpo sa_$s.in > log_wpo_$s.txt 2>&1
  echo "wpo $s done $(date +%T)"
  if grep -q FAIL0 log_wpo_$s.txt; then echo "FAIL0 start $s"; break; fi
done
echo ALLDONE
