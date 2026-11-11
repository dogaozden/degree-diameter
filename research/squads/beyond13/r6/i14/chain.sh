#!/bin/bash
# i14 chain: PSL(2,131) x Z139 orbit S (k=3 m=2 f=1), K=4, chained links from the r5/h12 cost-3 start.
B=/home/user/degree-diameter/research/frontier/beyond13
W=/home/user/degree-diameter/research/squads/beyond13/r6/i14
cd $W
S=/home/user/degree-diameter/research/squads/beyond13/r5/h12/a131_139_s9.txt.best
for link in $(seq 1 15); do
  seed=$((100 + link))
  OUT=$W/c131_L$(printf %02d $link)
  ORBIT="3 2 1" THREADS=1 START=$S timeout 105 nice -n 10 $B/bin/haar_big0 7 13 90 $seed 4 $OUT psl 131 139 > $OUT.log 2>&1
  grep RESULT $OUT.log >> $W/chain_results.txt
  if grep -q "best=0 " $OUT.log || [ -f "$OUT" -a "$(grep -c 'best=0 ' $OUT.log)" -gt 0 ]; then echo "SOLVED link $link" >> $W/chain_results.txt; break; fi
  if [ -f "$OUT.best" ]; then S=$OUT.best; fi
done
echo DONE >> $W/chain_results.txt
