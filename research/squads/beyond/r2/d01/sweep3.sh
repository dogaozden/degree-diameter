#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond/r2/d01
export THREADS=1 OMP_NUM_THREADS=1
for spec in "zn21 1" "zn21 2" "zn22 1"; do
  set -- $spec
  tag=c21_$1_s$2
  timeout 900 nice -n 10 ./mlift_chart k33m_base.txt $1.txt pat_s21.txt 150 $2 2.0 $tag.edges > run_$tag.log 2>&1
  echo "exit $?" >> run_$tag.log
  echo "done $tag: $(head -1 run_$tag.log)" >> sweep3.log
  if grep -q "best_cost=0" run_$tag.log; then echo "FOUND $tag" >> sweep3.log; break; fi
done
echo ALLDONE >> sweep3.log
