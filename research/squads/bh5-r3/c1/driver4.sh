#!/bin/bash
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
cd $C
for o in 1758 1845 1770; do
  echo "START $o $(date +%T)"
  timeout 300 nice -n 10 ./sweep.sh $o 3 7
  echo "END $o rc=$? $(date +%T)"
done
echo DRIVER_DONE $(date +%T)
