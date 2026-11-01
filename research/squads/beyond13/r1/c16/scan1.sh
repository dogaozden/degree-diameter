#!/bin/bash
# c16 scan: haar_gen3 random S (no orbits), d=4 D=13, non-SL/PSL(2,p) x Z_n families at matched |G|
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r1/c16
for spec in "pgl 41" "pgl 43" "psl 53" "pgl 47" "psl 59" "psl 61" "pgl 53" "sl 49" "psl 67" "pgl 59"; do
  name=$(echo $spec | tr ' ' '_')
  THREADS=1 nice -n 10 timeout 200 $B/bin/haar_gen3 4 13 60 7 8 s1_$name.sol $spec 1 > s1_$name.log 2>&1
  echo "$spec: $(grep -h RESULT s1_$name.log) $(grep -h 'full diameter' s1_$name.log)" >> scan1.summary
done
echo DONE >> scan1.summary
