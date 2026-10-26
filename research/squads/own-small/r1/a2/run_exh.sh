#!/bin/bash
# run_exh.sh BASEFILE TAG: exhaustive Aut/Stab-reduced 3+3 eval over all 15 groups of order 136 (LIMIT=2 prints cost<=2)
cd /home/user/degree-diameter/research/squads/own-small/r1/a2
for g in $(seq 1 15); do
  LIMIT=2 ./fenum bases/$1.txt groups/g136/g136_$(printf %04d $g).bin 3 10 enum groups/s136_$g.txt > out/$1_g$g.lines 2> out/$1_g$g.err
  echo "group $g: $(cat out/$1_g$g.err)"
done
