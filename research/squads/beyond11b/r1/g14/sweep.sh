#!/bin/bash
# usage: sweep.sh D B n secs seedbase ngroups ; runs lift on up to ngroups metacyclic groups of order n, sequentially
D=$1; B=$2; n=$3; secs=$4; sb=$5; ng=$6
i=0
python3 groups.py $n | shuf -n $ng --random-source=<(yes $sb) | while read M K R; do
  i=$((i+1))
  timeout 105 nice -n 10 ./lift $M $K $R $B $D $secs $((sb+i)) g14_found_D${D}_B${B}_n${n}_${M}_${K}_${R}.txt
done
