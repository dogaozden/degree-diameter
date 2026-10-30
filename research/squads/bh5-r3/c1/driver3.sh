#!/bin/bash
# c1 rerun, continuation: waits for driver2, then runs any lost order still without RESULT lines; deadline $1
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
S=$C/logs/sweep_h3_d7.txt
DEADLINE=$1
cd $C
until grep -q DRIVER_DONE /home/user/degree-diameter/research/squads/bh5-r3/c1/driver2.log; do sleep 3; done
for o in 1809 1806 1812 1815 1818 1827 1830 1842 1755 1746 1740 1752 1782 1776 1764 1836; do
  if [ $(grep -c "sg${o}_" $S) -gt 0 ]; then continue; fi
  if [ $(date +%s) -ge $DEADLINE ]; then echo "STOP before $o $(date +%T)"; break; fi
  echo "START $o $(date +%T)"
  timeout 600 nice -n 10 ./sweep.sh $o 3 7
  echo "END $o rc=$? $(date +%T)"
done
echo DRIVER_DONE $(date +%T)
