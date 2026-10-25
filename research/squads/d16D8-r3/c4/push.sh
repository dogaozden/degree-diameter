#!/bin/bash
# push.sh START_BASE START_M SECS SEED: one warm repair step per m (Z_m -> Z_(m+1)), continuing while VALID; logs each step.
T=/home/user/degree-diameter/research/d16D8
D=/home/user/degree-diameter/research/squads/d16D8-r3/c4
SRC=$D/m28_s1.src
cur=$1; m=$2; secs=$3; seed=$4
for i in 1 2; do
  nm=$((m+1))
  awk -v k=$nm 'NR==1{$2=k} {print}' $cur > $D/pw_$nm.base
  out=$D/pv_$nm.base
  res=$(SRCFILE=$SRC THREADS=1 timeout 1500 nice -n 10 $T/symrepair $D/pw_$nm.base 8 $secs $seed $out 2>/dev/null | grep RESULT)
  b=$(echo "$res" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  full=$(THREADS=1 timeout 600 nice -n 10 $T/baselift eval $out 8 | sed -n 's/.*uncovered=\([0-9]*\).*/\1/p')
  echo "m=$nm warm seed=$seed secs=$secs orbit_uncovered=$b all_source_uncovered=$full base=$out" >> $D/push.log
  if [ "$b" != "0" ]; then echo "stop at m=$nm (best orbit=$b)" >> $D/push.log; exit 0; fi
  cur=$out; m=$nm
done
