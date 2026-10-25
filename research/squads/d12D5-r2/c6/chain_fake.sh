#!/bin/bash
# waits for the running N=24 batch (last run k3_004), then runs fake ceilings for N=25 and N=26, one at a time
cd /home/user/degree-diameter/research/squads/d12D5-r2/c6
D=/home/user/degree-diameter/research/d12D5
w=0
until grep -q best_cost fake_k3_004_z24.log 2>/dev/null || [ $w -ge 300 ]; do sleep 2; w=$((w+2)); done
for N in 25 26; do
  for X in 000 001 002 003 004; do
    s=$(date +%s)
    FAKE=1 DIAGBT=1 timeout 300 nice -n 10 $D/mlift_ejoint2 $D/bases3/k3_$X.txt $D/tables/z$N.txt 30 1 2 1.0 > fake_k3_${X}_z$N.log 2>&1
    rc=$?
    echo "k3_$X N=$N rc=$rc wall=$(( $(date +%s)-s ))s $(grep best_cost fake_k3_${X}_z$N.log | cut -c1-80)" >> fake_summary.txt
  done
done
echo "CHAIN DONE" >> fake_summary.txt
