#!/bin/bash
# (7,5): 2+2 lifts over few-involution groups (vl annealing, 30 s x 2 seeds x 3 bases)
cd "$(dirname "$0")"
gap -q fewinv7.g > groups.txt 2>&1
for g in sl23xc13 q16xc19 q8xc39 bo48xc7 q32xc10 sl23xc14 q8c4xc10 c4q8xc10; do for b in b22_16 b22_25 b22_34; do for s in 1 2; do
  r=$(SECS=30 SEED=$s OUT=sol_${b}_${g}_s$s.txt nice -n 3 ../src/vl $b.txt grp/fi_$g.txt 2>/dev/null | tail -1)
  echo "$g $b seed $s $r" >> screen7.txt
  case "$r" in *"best 0 "*) echo "HIT $g $b $s" >> screen7.txt;; esac
done; done; done
echo DONE >> screen7.txt
