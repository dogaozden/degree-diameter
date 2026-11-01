#!/bin/bash
# g11 driver v2: side B only; each chunk restarts from the best valid state. Odd chunks cool (T0 0.10),
# even chunks hot (T0 0.18) so that orbits can drop and insert moves open up.
cd /home/user/degree-diameter/research/squads/beyond-small/r5/g11
R=/home/user/degree-diameter/research/squads/beyond-small
EDGES=$R/data/d16D5_n33792.edges
POOLB=$R/r3/e04/poolB_run2.txt
for c in $(seq 2 ${NCHUNK:-8}); do
  seed=$((12000 + c))
  if [ $((c % 2)) -eq 0 ]; then T0=0.18; T1=0.05; else T0=0.10; T1=0.03; fi
  { echo STATE; awk '{printf "1 %d %d", int(NF/4), NF; for(i=1;i<=NF;i++) printf " %d", $i; printf "\n"}' valid_B.txt; } > state_cur.txt
  echo "=== chunk $c seed $seed T0=$T0 start $(date +%T) best=$(wc -l < valid_B.txt)" >> drive.log
  timeout 900 nice -n 10 ./anneal_b $EDGES /dev/null $POOLB startB.txt ${SECS:-200} $seed $T0 $T1 1.0 state_cur.txt valid_B.txt >> drive.log 2>&1
  echo "=== chunk $c end $(date +%T) best_now=$(wc -l < valid_B.txt)" >> drive.log
done
echo DONE >> drive.log
