#!/bin/bash
T=/home/user/degree-diameter/research/squads/own-small/tools
cd /home/user/degree-diameter/research/squads/own-small/r1/w2
for g in $(seq -w 1 15); do
  GN=220 python3 randvolt.py $T/bases/cubic/b22_cubic.txt 200000 $((10#$g*7+1)) > v220_$g.txt
  $T/bin/flift $T/bases/cubic/b22_cubic.txt groups/b220/g220_$g.bin 3 10 eval < v220_$g.txt > c220_$g.txt
  python3 summ.py "220,$((10#$g))" c220_$g.txt
done
