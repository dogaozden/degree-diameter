#!/bin/bash
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r7/j05
prev=fresh_55_20_2.best
for i in 1 2 3; do
  env START=$prev THREADS=1 T0=6 T1=1 REHEAT=300 timeout 100 nice -n 10 $B/meta/hmeta 4 8 80 $((700+i)) 8 fin_55_20_2 55 20 2 > log_fin_$i.txt 2>&1
  echo "fin link $i: $(grep RESULT log_fin_$i.txt)" >> chain_fin.log
  if grep -q 'best=0 ' log_fin_$i.txt; then echo "SOLVED fin $i" >> chain_fin.log; break; fi
  prev=fin_55_20_2.best
done
echo DONE >> chain_fin.log
