#!/bin/bash
T=/home/user/degree-diameter/research/squads/own-small/tools
cd /home/user/degree-diameter/research/squads/own-small/r1/w2
for N in 58 59 60 61 62 63 65 66 67 68 69 70 71; do
 for id in $(seq 1 30); do
  f=groups/b$N/g${N}_$(printf %02d $id).bin; [ -f $f ] || continue
  for s in 1 2 3; do
   GN=$N python3 randvolt.py base7_$s.txt 30000 $((N*100+id*7+s)) > vv.txt
   timeout 20 $T/bin/flift base7_$s.txt $f 3 10 eval < vv.txt > cc.txt
   python3 summ.py "$N,$id,b7_$s" cc.txt
  done
 done
done
