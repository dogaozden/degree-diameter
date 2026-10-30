#!/bin/bash
# c1 rerun: orders whose exports failed during the dc2_lib.g syntax-error window (about 20:02-20:06 UTC)
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
DEADLINE=$1
cd $C
for o in 1809 1806 1812 1815 1818 1827 1830 1842 1755 1746 1740 1752 1782 1776 1764 1836; do
  if [ $(date +%s) -ge $DEADLINE ]; then echo "STOP before $o $(date +%T)"; break; fi
  echo "START $o $(date +%T)"
  timeout 600 nice -n 10 ./sweep.sh $o 3 7
  echo "END $o rc=$? $(date +%T)"
done
echo DRIVER_DONE $(date +%T)
