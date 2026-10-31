#!/bin/bash
cd /home/user/degree-diameter/research/squads/sd5c-r1/c1
for g in "298 20 193 149" "302 20 59 151"; do
  set -- $g
  tag="nsmeta_$1_$2_$3_$4"
  timeout 900 nice -n 10 env K=13 TYPES=1,3 SECS=20 STOPFIRST=1 MAXSOL=1 TBUDGET=150 ./fsd_x nsmeta $1 $2 $3 $4 > log_$tag.txt 2>&1
  echo "rc=$? group $tag" >> run_ns_status.txt
done
echo ALLDONE >> run_ns_status.txt
