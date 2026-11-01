#!/bin/bash
# g11 driver: side B only. Each chunk restarts from the best valid state (reset), anneals, keeps best in valid_B.txt.
cd /home/user/degree-diameter/research/squads/beyond-small/r5/g11
R=/home/user/degree-diameter/research/squads/beyond-small
EDGES=$R/data/d16D5_n33792.edges
POOLB=$R/r3/e04/poolB_run2.txt
for c in $(seq 1 ${NCHUNK:-8}); do
  seed=$((12000 + c))
  # reset state to current best valid (STATE header, side 1, ng=n/4, local=global ids)
  { echo STATE; awk '{printf "1 %d %d", int(NF/4), NF; for(i=1;i<=NF;i++) printf " %d", $i; printf "\n"}' valid_B.txt; } > state_cur.txt
  echo "=== chunk $c seed $seed start $(date +%T) best=$(wc -l < valid_B.txt)" >> drive.log
  timeout 900 nice -n 10 ./anneal_b $EDGES /dev/null $POOLB startB.txt ${SECS:-240} $seed ${T0:-0.25} ${T1:-0.05} ${LAM:-1.0} state_cur.txt valid_B.txt >> drive.log 2>&1
  echo "=== chunk $c end $(date +%T) best_now=$(wc -l < valid_B.txt)" >> drive.log
done
echo DONE >> drive.log
