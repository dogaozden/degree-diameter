#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r2/c4
for g in 304_41 304_42 304_35 304_29 304_34 312_55 312_60 312_61 312_39 320_102 320_104 320_6 320_C2^6xC5 320_D64xC5; do
  for b in b1 b2 b3; do
    f=grp/sg_$g.txt
    r=$(D=5 SECS=15 SEED=1 OUT=sols/${g}_${b}.sol ./vl $b.txt "$f" 2>/dev/null | grep RESULT)
    echo "$g $b $r"
  done
done
echo SCREEN_DONE
