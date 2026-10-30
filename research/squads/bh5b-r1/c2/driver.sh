#!/bin/bash
cd /home/user/degree-diameter/research/squads/bh5b-r1/c2
for n in 1857 1869 1878 1875 1881 1854 1884; do
  echo "== $n $(date +%T)"
  ./sweep.sh $n 3 7 20 "[1..NrSmallGroups($n)]" 1
done
echo "DRIVER DONE $(date +%T)"
