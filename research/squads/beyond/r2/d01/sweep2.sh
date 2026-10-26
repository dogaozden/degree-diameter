#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond/r2/d01
while kill -0 1389 2>/dev/null; do sleep 2; done
export THREADS=1 OMP_NUM_THREADS=1
for spec in "gD11 1" "gF21 1" "gD11 2" "gF21 2"; do
  set -- $spec
  tag=$1_s$2
  timeout 900 nice -n 10 ./mlift_chart k33m_base.txt $1.txt pat5_s11.txt 150 $2 2.0 $tag.edges > run_$tag.log 2>&1
  echo "exit $?" >> run_$tag.log
  echo "done $tag: $(head -1 run_$tag.log)" >> sweep2.log
done
echo ALLDONE >> sweep2.log
