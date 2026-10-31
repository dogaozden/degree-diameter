#!/bin/bash
# run_batch.sh N SECS TAG: 3 seeds of local-move SA from random starts, one after another (one heavy process at a time)
n=$1; secs=$2; tag=$3
for s in 1 2 3; do
  nice -n 10 ./ls7 $n $((s*97+n)) $secs 4 1.5 60 0 2 - out/${tag}_s$s.edges > out/${tag}_s$s.log
  tail -1 out/${tag}_s$s.log
done
