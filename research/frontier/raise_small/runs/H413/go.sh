#!/bin/bash
# (4,13) fresh hmeta seeds on Z1163 x|_102 Z83 (N = 96,529; r3/e10 reached cost 2)
cd /home/user/degree-diameter/research/frontier/raise_small
for s in $(seq 2001 2040); do
  out=runs/H413/s$s
  res=$(THREADS=1 T0=8 T1=1 REHEAT=400 timeout 400 bin/hmeta 4 13 70 $s 16 $out 1163 83 102 2>/dev/null | grep RESULT)
  echo "seed $s $res" >> runs/H413/log.txt
  if [ -f $out ] && ! [ -f $out.best ] || grep -q "best=0 " <<< "$res"; then python3 tools/metacheck.py $out >> runs/H413/log.txt 2>&1; break; fi
done
