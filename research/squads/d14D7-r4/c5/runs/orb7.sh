#!/bin/bash
# orbit cliques on q=7 and q=5 isometry orbits (heavy.sh slots, sequential)
cd /home/user/degree-diameter/research/squads/d14D7-r4/c5/units
HV=/home/user/degree-diameter/research/squads/bin/heavy.sh
for p in q7_s1_k3_t8 q7_s1_k3_t4 q7_s1_k3_t2; do
  $HV 60 ./orbitclique7 ../data/E7.map ../perms/$p.txt 40 1 ../runs/orb_$p.flags > ../runs/orb_$p.log 2>&1
  CHECKONLY=1 ./pack ../data/gh_7.txt 0 1 /dev/null ../runs/orb_$p.flags > ../runs/orb_$p.check 2>&1
done
for p in q5_s1_k3_t2 q5_s1_k3_t4 q5_s2_k4_t6 q5_s3_k4_t6; do
  $HV 40 ./orbitclique5 ../data/E5.map ../perms/$p.txt 20 1 ../runs/orb_$p.flags > ../runs/orb_$p.log 2>&1
  CHECKONLY=1 ./pack ../data/gh_5.txt 0 1 /dev/null ../runs/orb_$p.flags > ../runs/orb_$p.check 2>&1
done
echo done > ../runs/orb7.done
