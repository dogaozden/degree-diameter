#!/bin/bash
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r1/c18
for pair in "b22_t2 meta:55:10:4" "b22_t1 meta:55:10:4" "b22_t2 meta:49:12:19"; do
  set -- $pair
  tag=long_${1}_$(echo $2 | tr ':' '_')
  line=$(THREADS=1 QUIET=1 timeout 120 nice -n 10 $T/lift $T/bases/$1.txt $2 4 8 40 2 8 $D/runs/$tag.sol 2>&1 | grep RESULT)
  echo "$1 $2 :: $line"
done
