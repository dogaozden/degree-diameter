#!/bin/bash
# fake-chart screen: controller ceiling only (every walk nonsingular, every pencil complete). One run at a time.
cd /home/user/degree-diameter/research/squads/d12D5-r1/c7
MLC=/home/user/degree-diameter/research/d12D5/mlift_chart
FAKE=/home/user/degree-diameter/research/d12D5/charts/fake_univ.txt
OUT=out/fake_summary.txt
: > $OUT
run() { # base table
  local b=$1 t=$2
  r=$(THREADS=1 timeout 90 nice -n 10 $MLC bases/$b.txt tables/$t.txt $FAKE 8 1 2>&1 | grep best_cost | sed 's/ volt=.*//')
  echo "$b $t :: $r" >> $OUT
}
run k1_k1 cyc67; run k1_k1 cyc70; run k1_k1 dih35; run k1_k1 dih34; run k1_k1 dih36; run k1_k1 cyc72; run k1_k1 meta7_10_6
for b in k5_s5_0 k5_s5_1; do for t in cyc14 dih7; do run $b $t; done; done
for b in k6_s6_0 k6_s6_1; do for t in cyc12 dih6 dicyc3; do run $b $t; done; done
for b in k7_s7_0 k7_s7_1; do for t in cyc10 dih5; do run $b $t; done; done
for t in cyc9 z3z3; do run k8_s8_0 $t; done
for t in cyc8 dih4 dicyc2; do run k9_s9_0 $t; done
for b in k10_s10_0 k10_s10_1; do run $b cyc7; done
for b in k12_s12_0 k12_s12_1; do for t in cyc6 dih3; do run $b $t; done; done
run k14_s14_0 cyc5
run k16_s16_0 cyc5
echo DONE >> $OUT
