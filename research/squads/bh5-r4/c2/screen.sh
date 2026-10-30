#!/bin/bash
# 20 s vl screen of b6/b33_9.txt over the non-abelian order-60 groups (except SmallGroup(60,3)), D=5, no SWAP
cd /home/user/degree-diameter/research/beyond-haar-d5
G=/home/user/degree-diameter/research/squads/bh5-r4/c2
for i in 1 2 5 6 7 8 9 10 11 12; do
  r=$(D=5 SECS=20 SEED=1 OUT=$G/screen_g$i.sol timeout 60 nice -n 10 ./vl b6/b33_9.txt $G/groups/sg_60_$i.txt 2>/dev/null | grep RESULT)
  echo "g$i $(cat $G/groups/sg_60_$i.name) $r" >> $G/screen.txt
done
