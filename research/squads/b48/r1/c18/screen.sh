#!/bin/bash
# screen: 12 metacyclic groups x 2 bases (2+2 bases), lift annealing 7 s each, one seed
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r1/c18
GRPS="meta:55:10:4 meta:73:8:10 meta:97:6:36 meta:95:6:31 meta:49:12:19 meta:48:12:5 meta:29:20:12 meta:24:24:5 meta:145:4:12 meta:99:6:23 meta:98:6:19 meta:75:8:7"
for B in b22_t1 b22_t2; do
  for G in $GRPS; do
    tag=${B}_$(echo $G | tr ':' '_')
    line=$(THREADS=1 QUIET=1 timeout 120 nice -n 10 $T/lift $T/bases/$B.txt $G 4 8 7 1 8 $D/runs/$tag.sol 2>&1 | grep RESULT)
    echo "$B $G :: $line"
  done
done
