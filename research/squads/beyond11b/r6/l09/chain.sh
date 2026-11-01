#!/bin/bash
# sequential resume chain, one process at a time; each link: START -> SAVEBEST
B=/home/user/degree-diameter/research/squads/beyond11b/bin
cd /home/user/degree-diameter/research/squads/beyond11b/r6/l09
SPEC="8 11"
prev=b2.txt
i=3; seed=31
for mode in tfull plain tfull plain tfull plain; do
  out=b$i.txt
  if [ $mode = tfull ]; then ENVX="TFULL=1 TARGP=100 TMAX=0.6"; else ENVX="TMAX=0.6"; fi
  echo "link $i mode=$mode start=$prev seed=$seed $(date +%T)" >> runs.txt
  env START=$PWD/$prev SAVEBEST=$PWD/$out $ENVX THREADS=1 timeout 105 nice -n 10 $B/haar_gen3t $SPEC 60 $seed 4 $PWD/sol_s$seed.txt meta 371857 61 153765 1 > r$i.out 2>&1
  echo "exit $? $(date +%T)" >> r$i.out
  tail -1 r$i.out >> runs.txt
  prev=$out; i=$((i+1)); seed=$((seed+1))
done
echo CHAIN_DONE >> runs.txt
