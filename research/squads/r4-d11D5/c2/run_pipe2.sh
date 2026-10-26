#!/bin/bash
# card c2, round r4-d11D5, revised per coordinator: long po7 anneal (T0=8, T1=0.3) from the start-20 state until
# cost <= 20, then wpo. Up to two po7 rounds. wpo is not started from a state above cost 20.
cd /home/user/degree-diameter/research/squads/r4-d11D5/c2
cur=sa_20.in
for r in 1 2; do
  out=sa_r${r}_20.in
  timeout 1500 nice -n 10 env THREADS=1 SECS=600 T0=8 T1=0.3 OUT=$out OUT0=fail0_n587_sa_r${r}_20.in ./po7 $cur > log_sa_r${r}_20.txt 2>&1
  c=$(grep RESULT log_sa_r${r}_20.txt | sed -E 's/.*best=([0-9]+).*/\1/')
  echo "po7 round $r best=$c $(date +%T)"
  if grep -q FAIL0 log_sa_r${r}_20.txt; then echo "FAIL0 in po7 round $r"; cp fail0_n587_sa_r${r}_20.in fail0_n587.in; echo ALLDONE2; exit 0; fi
  cur=$out
  if [ "$c" -le 20 ]; then
    timeout 1500 nice -n 10 env THREADS=1 SECS=600 SEED=1 OUT=out_20.in OUT0=fail0_n587_s20.in ./wpo $out > log_wpo_20.txt 2>&1
    echo "wpo done $(date +%T)"
    if grep -q FAIL0 log_wpo_20.txt; then echo "FAIL0 in wpo"; cp fail0_n587_s20.in fail0_n587.in; fi
    break
  fi
done
echo ALLDONE2
