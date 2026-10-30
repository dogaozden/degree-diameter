#!/bin/bash
# c8: Haar annealing (mcos TYPE=1|1) over non-abelian groups of order 352-360 with > 3 involutions.
# Pass 1: SECS=6 per group, ascending involution count, until the pass-1 deadline. Pass 2: top 4 by cost, SECS=120, SEED=2.
C=/home/user/degree-diameter/research/s65/tools
G=/home/user/degree-diameter/research/s65/groups/mc
W=/home/user/degree-diameter/research/squads/s65r3/c8
cd $W && mkdir -p p1 p2
DEADLINE=$(( $(date +%s) + 22*60 ))
: > p1/summary.txt
while read b inv name; do
  if [ $(date +%s) -ge $DEADLINE ]; then echo "DEADLINE_STOP before $b" >> p1/summary.txt; break; fi
  TYPE="1|1" SECS=6 SEED=1 EDGES=$W/p1/$b.edges timeout 120 nice -n 10 $C/mcos $G/$b.txt > p1/$b.log 2>&1
  c=$(grep -h '^COMB' p1/$b.log | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}')
  echo "$b $inv ${c:-NA} $name" >> p1/summary.txt
  if [ "$c" = "0" ]; then echo "CANDIDATE_COST0 $b" >> p1/summary.txt; fi
done < $W/groups_sel.txt
echo "PASS1_END $(date +%T)" >> p1/summary.txt
# pass 2: four lowest costs (stable, so ties keep the ascending-involution order)
grep -v -e '^DEADLINE' -e '^PASS1' -e '^CANDIDATE' p1/summary.txt | awk '$3!="NA"' | sort -k3,3n -s | head -4 > p2/top4.txt
while read b inv c name; do
  TYPE="1|1" SECS=120 SEED=2 EDGES=$W/p2/$b.edges timeout 200 nice -n 10 $C/mcos $G/$b.txt > p2/$b.log 2>&1
  c2=$(grep -h '^COMB' p2/$b.log | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}')
  echo "$b $inv p1cost=$c p2cost=${c2:-NA}" >> p2/summary.txt
done < p2/top4.txt
echo "PASS2_END $(date +%T)" >> p2/summary.txt
