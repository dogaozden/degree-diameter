#!/bin/bash
# sequential SA screen of nonabelian groups of order 192..196 on the PG(2,3) incidence base
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
for g in g1 g2 g3 g4 g5 g6 ; do
  echo "== $g" 
  nice -n 10 ./hg pg23.txt groups/$g.bin 40 11 150 1.5 scr_$g 2>&1 | grep -E "start|RESULT"
done
echo DONE
