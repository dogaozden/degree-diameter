#!/bin/bash
# quick survey: base A and B on a list of metacyclic groups, 2.5 s each
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r1/c33
for g in 137:8:136 137:8:37 274:4:37 547:2:546 55:20:12 55:20:21 110:10:31 25:44:7 22:50:3 61:18:13 183:6:13 92:12:45 138:8:47 31:36:5 93:12:25 29:38:28 37:30:10 185:6:26 186:6:25 11:100:3; do
  for b in A B; do
    r=$(THREADS=1 timeout 120 nice -n 10 $T/lift base$b.txt meta:$g 4 8 2.5 7 2>&1 | grep RESULT)
    echo "base=$b meta:$g $r"
  done
done
