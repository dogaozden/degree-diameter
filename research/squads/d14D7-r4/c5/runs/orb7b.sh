#!/bin/bash
# second batch: more q=7 isometry orbit cliques (30 s each); starts after orb7.sh has finished its q=7 part
cd /home/user/degree-diameter/research/squads/d14D7-r4/c5/units
HV=/home/user/degree-diameter/research/squads/bin/heavy.sh
while [ ! -f ../runs/orb7.done ]; do sleep 3; done
for p in q7_s2_k2_t8 q7_s3_k2_t8 q7_s4_k4_t8 q7_s5_k2_t8 q7_s6_k3_t8 q7_s7_k4_t8 q7_s2_k3_t8 q7_s1_k2_t4 q7_s1_k3_t4 q7_s4_k3_t4; do
  [ -f ../perms/$p.txt ] || continue
  $HV 60 ./orbitclique7 ../data/E7.map ../perms/$p.txt 30 1 ../runs/orb_$p.flags > ../runs/orb_$p.log 2>&1
  CHECKONLY=1 ./pack ../data/gh_7.txt 0 1 /dev/null ../runs/orb_$p.flags > ../runs/orb_$p.check 2>&1
done
echo done > ../runs/orb7b.done
