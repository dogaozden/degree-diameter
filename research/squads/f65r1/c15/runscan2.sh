#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c15
for f in work/*.txt; do
  b=$(basename $f .txt)
  [ -f work/$b.scan ] && continue
  case $b in A5xA5*|A5xS3xZ3*) continue;; esac
  timeout 900 nice -n 10 ./bicoset $f 6 5 work/$b 7000000 > work/$b.scan 2>&1
  tail -1 work/$b.scan
done
echo SCAN2DONE
