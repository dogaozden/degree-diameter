#!/bin/bash
# g11: exact all-source runs of the bound program (every source, both D) for all bases; writes res/*.txt
cd /home/user/degree-diameter/research/squads/beyond13/r4/g11
mkdir -p res2
for f in pg23_levi gq33_levi k44; do for D in 13 14; do
  nice -n 10 ./lbound bases/$f.edges $D 1 > res2/$f.D$D.txt 2>&1
done; done
for f in gp8_3 heawood gp10_3 gp12_5 gp14_3 gp14_5 gp16_3 gp16_5 gp18_5 gp20_3 gp20_7 gp24_5 gp30_7 tutte8 rnd10_1 rnd12_0 rnd24_1; do for D in 13 14; do
  nice -n 10 ./lbound bases/$f.edges $D 1 > res2/$f.D$D.txt 2>&1
done; done
echo done > res2/all.done
