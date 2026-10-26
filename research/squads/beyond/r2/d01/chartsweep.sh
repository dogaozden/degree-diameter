#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond/r2/d01
export THREADS=1 OMP_NUM_THREADS=1
for s in 21 22; do
  timeout 900 nice -n 10 ./chart5 150 $s 5 chart_s$s.txt > chart_s$s.log 2>&1
  echo "exit $?" >> chart_s$s.log
  echo "done chart $s: $(grep final chart_s$s.log)" >> chartsweep.log
done
echo ALLDONE >> chartsweep.log
