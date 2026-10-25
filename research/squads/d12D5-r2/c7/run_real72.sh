#!/bin/bash
# card c7: real runs at m = 72 (k = 4, Z_18), chart held fixed (PV = 1.0), one run at a time
B=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r2/c7
S=$C/real/summary.txt
# wait until the fake-ceiling batch (g19 runs) has finished, so only one heavy run is active
while ps -eo args | grep -v grep | grep -q "c7/g19.txt"; do sleep 5; done
run() {  # name base table chart seed
  name=$1; base=$2; tab=$3; chart=$4; seed=$5; out=$C/real/$name
  WRITEBEST=1 DIAGBT=1 INIT_ECHART=$chart timeout 600 nice -n 10 $B/mlift_ejoint2 $base $tab 120 $seed 2 1.0 $out > $out.log 2>&1
  echo "$name $(grep -o 'm=[0-9]* best_cost=[0-9]*' $out.log)" >> $S
  if grep -q 'best_cost=0 ' $out.log; then
    python3 $B/elift.py $out.edges $out.echart $out.lift.edges >> $out.log 2>&1
    $B/apsp $out.lift.edges 12 5 > $out.apsp.txt 2>&1
    echo "$name APSP $(grep -o 'RESULT.*' $out.apsp.txt)" >> $S
    grep -q 'RESULT VALID' $out.apsp.txt || rm -f $out.lift.edges
  fi
}
run r012_g18_s2 $B/bases4/k4_012.txt $C/g18.txt $B/diag/bt_k4_012_0.echart 2
run r019_g18_s2 $B/bases4/k4_019.txt $C/g18.txt $C/bt_k4_019_0.echart 2
run r017_g18_s2 $B/bases4/k4_017.txt $C/g18.txt $C/bt_k4_017_0.echart 2
run r023_g18_s2 $B/bases4/k4_023.txt $C/g18.txt $C/bt_k4_023_0.echart 2
echo "DONE $(date -u +%H:%M)" >> $S
