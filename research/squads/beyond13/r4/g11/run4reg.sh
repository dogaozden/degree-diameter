#!/bin/bash
# g11: 4-regular bases at D=13,14. Vertex-transitive side (PG(2,3) Levi graph: point 0 and line 13; GQ(3,3) Levi graph:
# point 0 and line 40, as two orbit representatives; sources 1 and 41 are also run as a cross-check).
cd /home/user/degree-diameter/research/squads/beyond13/r4/g11
nice -n 10 ./lbound bases/pg23_levi.edges 13 1 0,13,1 > res/pg23_levi.D13.txt 2>&1
nice -n 10 ./lbound bases/pg23_levi.edges 14 1 0,13,1 > res/pg23_levi.D14.txt 2>&1
nice -n 10 ./lbound bases/gq33_levi.edges 13 1 0,40,1,41 > res/gq33_levi.D13.txt 2>&1
nice -n 10 ./lbound bases/gq33_levi.edges 14 1 0,40,1,41 > res/gq33_levi.D14.txt 2>&1
nice -n 10 ./lbound bases/k44.edges 13 1 > res/k44.D13.txt 2>&1
nice -n 10 ./lbound bases/k44.edges 14 1 > res/k44.D14.txt 2>&1
echo done > res/4reg.done
