#!/bin/bash
# chain.sh d D m k r links tag  -- chained hmeta runs, START from previous .best, stops at cost 0
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r7/j05
d=$1; D=$2; m=$3; k=$4; r=$5; L=$6; tag=$7
prev=""
for i in $(seq 1 $L); do
  seed=$((100 + i * 7 + m))
  out=sol_${tag}
  if [ -n "$prev" ]; then
    env START=$prev THREADS=1 T0=8 T1=1 REHEAT=400 timeout 100 nice -n 10 $B/meta/hmeta $d $D 90 $seed 8 $out $m $k $r > log_${tag}_$i.txt 2>&1
  else
    env THREADS=1 T0=8 T1=1 REHEAT=400 timeout 100 nice -n 10 $B/meta/hmeta $d $D 90 $seed 8 $out $m $k $r > log_${tag}_$i.txt 2>&1
  fi
  echo "link $i: $(grep RESULT log_${tag}_$i.txt)" >> chain_${tag}.log
  if grep -q 'best=0 ' log_${tag}_$i.txt; then echo "SOLVED link $i" >> chain_${tag}.log; break; fi
  prev=$out.best
done
echo DONE >> chain_${tag}.log
