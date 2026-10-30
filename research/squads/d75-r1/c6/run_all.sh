#!/bin/bash
# card c6 driver: affine-map search over the assigned groups, one process at a time
cd /home/user/degree-diameter/research/squads/d75-r1/c6
export TMPDIR=$PWD/tmp
for g in 605_4 609_1 603_1 603_3 651_1 651_2 651_3 651_4 657_1 657_3 657_4 624_1 624_2 624_3 624_4 624_5 624_7 624_12 624_22 624_24 624_25 624_41 624_42 624_43; do
  CAP=20000000 TLIM=${TL:-60} timeout 400 nice -n 10 ./affine75 tmp/g$g.aff > tmp/out_$g.txt 2> tmp/err_$g.txt
  echo "$g $(grep SUMMARY tmp/out_$g.txt)" >> tmp/all_summary.txt
  if grep -q VALID tmp/out_$g.txt; then echo "VALID $g" >> tmp/all_summary.txt; fi
done
echo ALLDONE >> tmp/all_summary.txt
