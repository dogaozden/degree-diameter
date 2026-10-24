#!/bin/bash
# RANDORB screen: each group x orbit type, 2M random symmetric S (near-exhaustive for these orbit spaces)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r1/c6
cd $C
while read -r GRP; do
  tag=$(echo $GRP | tr ' ' '_')
  for ORB in "3 2 0" "2 3 0" "6 1 0"; do
    ot=$(echo $ORB | tr ' ' '')
    ORBIT="$ORB" RANDORB=2000000 timeout 900 nice -n 10 $B/haar_sym 6 5 1 1 8 $C/s_${tag}_${ot}.txt $GRP > $C/logs/r_${tag}_${ot}.log 2>&1
    echo "== $GRP | ORBIT=$ORB :: $(grep -h -E 'alpha:|ORBIT k=|RANDORB d=' $C/logs/r_${tag}_${ot}.log | sed 's/RANDORB hist.*//' | tr '\n' ' ')"
  done
done <<'LIST'
psl 3 31 1
psl 5 6 1
sl 5 3 1
pgl 5 3 1
psl 9 1 1
sl 3 15 1
pgl 3 15 1
psl 3 30 1
psl 3 29 1
psl 3 32 1
sl 3 16 1
pgl 3 16 1
psl 3 33 1
psl 5 7 1
LIST
