#!/bin/bash
# merge.sh ORBA OUTPREFIX : A-orbit file (B-vertex bases) + the 21 B-orbits of r3/orbAB_27_21.txt (lines 28-48)
D=/home/user/degree-diameter/research/squads/beyond-small/r3/e10
cd $D
cat "$1" > $2.orb
tail -21 ../orbAB_27_21.txt >> $2.orb
python3 build_orbits.py $2.orb $2.edges
timeout 100 nice -n 10 ../../bin/apsp $2.edges 17 5 | tail -2
