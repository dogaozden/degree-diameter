#!/bin/sh
# usage: run_jobs.sh FIRST LAST SECS K   (runs job lines FIRST..LAST of jobs.txt; appends RESULT lines to screen.txt)
cd /home/user/degree-diameter/research/squads/deep-65b/round1/c5
sed -n "$1,$2p" jobs.txt | while read o id a; do
  r=$(nice -n 15 ./pathsplit tabs/sg_${o}_${id}.tab $a 1 $3 - $4)
  name=$(cut -d' ' -f1-3 tabs/sg_${o}_${id}.name | tr ' ' '_')
  echo "$o $id $a $name $r" >> screen.txt
done
