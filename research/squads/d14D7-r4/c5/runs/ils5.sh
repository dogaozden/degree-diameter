#!/bin/bash
# q=5 spread ILS, several seeds, 60 s each (heavy.sh slots)
cd /home/user/degree-diameter/research/squads/d14D7-r4/c5/units
for s in 101 102 103 104; do
  /home/user/degree-diameter/research/squads/bin/heavy.sh 90 ./spreadpack ../data/gh_5.txt ../data/coords5.txt 2 60 $s ../runs/q5_ils_s$s.flags 2> ../runs/q5_ils_s$s.log
  CHECKONLY=1 ./pack ../data/gh_5.txt 0 1 /dev/null ../runs/q5_ils_s$s.flags > ../runs/q5_ils_s$s.check 2>&1
done
echo done > ../runs/ils5.done
