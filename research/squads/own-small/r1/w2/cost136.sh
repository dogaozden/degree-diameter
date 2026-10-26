#!/bin/bash
T=/home/user/degree-diameter/research/squads/own-small/tools
cd /home/user/degree-diameter/research/squads/own-small/r1/w2
# base 3+3 (6 vertices): 136 groups from GAP (ids 1..15) plus meta:17:8:4
for g in $(seq -w 1 15); do
  GN=136 python3 randvolt.py /home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt 100000 $((10#$g*13+5)) > v136_$g.txt
  $T/bin/flift /home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt groups/b136/g136_$g.bin 3 10 eval < v136_$g.txt > c136_$g.txt
  python3 summ.py "136,$((10#$g))" c136_$g.txt
done
GN=136 python3 randvolt.py /home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt 100000 99 > v136_meta.txt
$T/bin/flift /home/user/degree-diameter/research/squads/own-small/seeds/base33_0.txt meta:17:8:4 3 10 eval < v136_meta.txt > c136_meta.txt
python3 summ.py "136,meta17_8_4" c136_meta.txt
