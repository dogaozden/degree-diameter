#!/bin/bash
cd /home/user/degree-diameter/research/squads/gqd5-r1/c3
for s in 11 12; do
  nice -n 10 timeout 300 ./mis tabu $s 150 out_tabu_$s.txt 60 >> log_tabu.txt 2>&1
  nice -n 10 timeout 300 ./mis arw $s 150 out_arw_$s.txt >> log_arw.txt 2>&1
done
echo ALLDONE >> log_arw.txt
