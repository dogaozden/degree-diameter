#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond/r2/d01
export THREADS=1 OMP_NUM_THREADS=1
for spec in "k44_base.txt zn16 2 1" "k44_base.txt zn16 3 2" "k33m_base.txt zn21 2 2" "k33m_base.txt zn21 3 3" "k33m_base.txt zn22 2 2" "k44_base.txt zn17 4 1"; do
  set -- $spec
  base=$1; zn=$2; seed=$3; tag=$(echo "$1_$2_s$seed" | sed 's/_base.txt//;s/\.txt//')
  timeout 900 nice -n 10 ./mlift_chart $base $zn.txt pat5_s11.txt 150 $seed 2.0 $tag.edges > run_$tag.log 2>&1
  echo "exit $?" >> run_$tag.log
  echo "done $tag: $(head -1 run_$tag.log)" >> sweep1.log
done
echo ALLDONE >> sweep1.log
