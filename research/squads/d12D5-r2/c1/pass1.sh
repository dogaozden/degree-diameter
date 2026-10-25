#!/bin/bash
# Card c1, Haiku squad round 2, cell (12,5): first pass, one 120 s run per K33m backtrack-complete chart.
# K33m over Z_24 (m = 72), PV = 1.0 (chart fixed), DIAGBT = 1, T0 = 2 for all charts, seeds 721..733.
C=/home/user/degree-diameter/research/squads/d12D5-r2/c1
D=/home/user/degree-diameter/research/d12D5
seed=721
for ch in bt_k33m_0 bt_k33m_1 bt_k33m_2 bt_k33m_3 bt2_k33m_0 bt2_k33m_1 bt2_k33m_2 bt3_k33m_0 bt3_k33m_1 bt3_k33m_2 bt4_k33m_0 bt4_k33m_1 bt4_k33m_2; do
  out=$C/p1_${ch}_s${seed}_t2
  s=$(date -u +%H:%M:%S)
  WRITEBEST=1 DIAGBT=1 INIT_ECHART=$D/diag/$ch.echart timeout 600 nice -n 10 $D/mlift_ejoint2 $D/base_k33m.txt $D/tables/z24.txt 120 $seed 2 1.0 $out > $out.log 2>&1
  bc=$(grep -o 'best_cost=[0-9]*' $out.log | head -n 1)
  echo "$ch seed=$seed T0=2 PV=1.0 ${bc:-best_cost=NA} start=$s end=$(date -u +%H:%M:%S)" >> $C/runs.txt
  seed=$((seed+1))
done
echo "PASS1 DONE $(date -u +%H:%M:%S)" >> $C/runs.txt
