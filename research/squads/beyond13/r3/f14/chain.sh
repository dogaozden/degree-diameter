#!/bin/bash
# f14: chain haar_big0 links on SL(2,541) x Z1, orbit 3 2 1, d=7 D=13, starting from the r2/e10 best S (cost 10)
B=/home/user/degree-diameter/research/frontier/beyond13
W=/home/user/degree-diameter/research/squads/beyond13/r3/f14
cd $W
prev=$W/start541.best
for i in $(seq 1 ${LINKS:-13}); do
  out=$W/l$i.sol
  seed=$((7000 + i * 37))
  START=$prev ORBIT="3 2 1" THREADS=1 timeout 105 nice -n 10 $B/bin/haar_big0 7 13 90 $seed 4 $out sl 541 1 > $W/l$i.log 2>&1
  echo "link $i seed $seed: $(grep RESULT $W/l$i.log | cut -c1-200)" >> $W/chain.log
  if [ -s "$out" ] && grep -q "best=0" $W/l$i.log; then echo "FOUND cost 0 at link $i" >> $W/chain.log; break; fi
  if [ -s "$out.best" ]; then prev="$out.best"; fi
done
echo DONE >> $W/chain.log
