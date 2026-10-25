#!/bin/bash
# fake-chart screen, round 2 ordering: abelian groups first (all 3 bases each), then non-abelian; 10 s CPU, seed 1
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r1/c3
cd $C
out=screen/summary2.tsv
: > $out
tail --pid=5151 -f /dev/null
for t in tables/g34_cyc34.txt tables/g35_cyc35.txt tables/g36_cyc36.txt tables/g36_c6xc6.txt tables/g36_c3xc12.txt \
         tables/g36_c2xc18.txt tables/g37_cyc37.txt tables/g38_cyc38.txt; do
  for b in 1 2 3; do
    name=$(basename $t .txt)
    log=screen/k2_${b}_${name}_t10.log
    THREADS=1 timeout 120 nice -n 10 $D/mlift_chart $D/base_k2_${b}.txt $t $D/charts/fake_univ.txt 10 1 > $log 2>&1
    line=$(grep best_cost $log | head -1)
    if [ -z "$line" ]; then line="FAIL $(tail -1 $log)"; fi
    echo -e "base_k2_${b}\t${name}\t${line}" >> $out
  done
done
echo DONE_ABELIAN >> $out
for t in tables/g34_dih17.txt tables/g36_dih18.txt tables/g38_dih19.txt tables/g36_meta9_4_8.txt tables/g36_d3xd3.txt \
         tables/g36_c3xdicyc3.txt tables/g36_c2xmeta9_2_8.txt; do
  for b in 1 2 3; do
    name=$(basename $t .txt)
    log=screen/k2_${b}_${name}_t10.log
    THREADS=1 timeout 120 nice -n 10 $D/mlift_chart $D/base_k2_${b}.txt $t $D/charts/fake_univ.txt 10 1 > $log 2>&1
    line=$(grep best_cost $log | head -1)
    if [ -z "$line" ]; then line="FAIL $(tail -1 $log)"; fi
    echo -e "base_k2_${b}\t${name}\t${line}" >> $out
  done
done
echo DONE >> $out
