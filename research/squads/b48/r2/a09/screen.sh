#!/bin/bash
# screen each group: lift on the 2+2 base b22_t1, 1.5 s, seed 1
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r2/a09
while IFS=$'\t' read -r kind N spec name; do
  out=$(THREADS=1 timeout 120 nice -n 10 $T/lift $T/bases/b22_t1.txt grp/$name.bin 4 8 1.5 1 8 2>/dev/null | grep RESULT)
  best=$(echo "$out" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  echo -e "$name\t$N\t${best:-NA}" >> screen.txt
done < names.txt
