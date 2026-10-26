#!/bin/bash
# h10: screen classic cubic bases at (3,9) with flift (4 s each), from plan.txt made by gen.py
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r4/h10 && mkdir -p out
i=0; while read base b g; do i=$((i+1)); B=$T/bases/cubic/$base.txt
  r=$(THREADS=1 timeout 120 nice -n 10 $T/flift $B $g 3 9 4 $i 8 out/s_${i}.txt 2>/dev/null | grep RESULT)
  echo "$base $b $g | $r" >> screen.txt; done < plan.txt
