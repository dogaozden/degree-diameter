#!/bin/bash
# c3b screens: RANDORB=1000 on SL(q) x Z_n groups of the window, one at a time, after driver.sh has finished.
cd /home/user/degree-diameter/research/squads/handsoff-108/c3b-sl23x49
B=/home/user/degree-diameter/research/d10D8/sym2/haar_sym2
while [ ! -f driver.done ]; do sleep 20; done
seed=108461
for g in "sl 13 271" "sl 9 823" "sl 8 1171" "sl 7 1753" "sl 7 1777" "sl 5 4903" "sl 5 4921" "sl 7 1783"; do
  f=rand_$(echo $g | tr ' ' _).out
  ORBIT="3 3 1" ORBW=3 RANDORB=1000 THREADS=1 nice -n 10 timeout 900 $B 10 8 1 $seed 8 /dev/null $g > $f 2> ${f%.out}.err
  seed=$((seed+1))
done
echo done > screen.done
