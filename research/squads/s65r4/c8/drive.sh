#!/bin/bash
# card c8: tabu on 3+3 voltage lifts, 6 best round-1 (base, group) pairs, then 2 more seeds on the best 2
cd /home/user/degree-diameter/research/squads/s65r4/c8 || exit 1
T=/home/user/degree-diameter/research/s65/tools/tabu
G=/home/user/degree-diameter/research/s65/groups/sg
: > summary.txt
for p in sg_116_1:m05 sg_116_1:m16 sg_120_3:m15 sg_117_1:m06 sg_120_7:m05 sg_116_1:m08; do
  g=${p%%:*}; b=${p##*:}
  SECS=180 SEED=1 INIT=random timeout 400 nice -n 10 $T bases/$b.txt $G/$g.txt runs/${g}_${b}_s1.sol \
    > runs/${g}_${b}_s1.log 2> runs/${g}_${b}_s1.err
  echo "$g $b 1 $(awk '/^RESULT/{print $3}' runs/${g}_${b}_s1.log)" >> summary.txt
done
sort -k4,4n summary.txt | head -2 > top2.txt
while read g b s c; do
  SECS=180 SEED=2 INIT=random timeout 400 nice -n 10 $T bases/$b.txt $G/$g.txt runs/${g}_${b}_s2.sol \
    > runs/${g}_${b}_s2.log 2> runs/${g}_${b}_s2.err
  echo "$g $b 2 $(awk '/^RESULT/{print $3}' runs/${g}_${b}_s2.log)" >> summary.txt
done < top2.txt
echo DONE >> summary.txt
