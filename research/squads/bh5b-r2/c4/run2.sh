#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c4
for combo in "312_55 b2" "320_104 b2"; do
  set -- $combo
  g=$1; b=$2
  for s in 1 2; do
    r=$(D=5 SECS=120 SEED=$s OUT=sols/long_${g}_${b}_s$s.sol ./vl $b.txt grp/sg_$g.txt 2>/dev/null | grep RESULT)
    echo "$g $b seed$s $r"
  done
done
echo LONG_DONE
