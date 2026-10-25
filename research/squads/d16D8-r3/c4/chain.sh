#!/bin/bash
# chain.sh START_BASE START_M MAXM SECS SEED: warm-start chain Z_m -> Z_(m+1) (same voltages) + symrepair (SRCFILE).
# Stops at the first m where repair fails within SECS; logs best orbit-source uncovered and the all-source count.
T=/home/user/degree-diameter/research/d16D8
D=/home/user/degree-diameter/research/squads/d16D8-r3/c4
SRC=$D/m28_s1.src
cur=$1; m=$2; maxm=$3; secs=$4; seed=$5
while [ $m -lt $maxm ]; do
  nm=$((m+1))
  awk -v k=$nm 'NR==1{$2=k} {print}' $cur > $D/ws_$nm.base
  out=$D/chain_$nm.base
  res=$(SRCFILE=$SRC THREADS=1 timeout 1500 nice -n 10 $T/symrepair $D/ws_$nm.base 8 $secs $seed $out 2>/dev/null | grep RESULT)
  b=$(echo "$res" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  full=$(THREADS=1 timeout 600 nice -n 10 $T/baselift eval $out 8 | sed -n 's/.*uncovered=\([0-9]*\).*/\1/p')
  echo "m=$nm warm seed=$seed secs=$secs orbit_uncovered=$b all_source_uncovered=$full" >> $D/chain.log
  if [ "$b" != "0" ]; then echo "stop at m=$nm" >> $D/chain.log; exit 0; fi
  cur=$out; m=$nm
done
echo "reached maxm=$m" >> $D/chain.log
