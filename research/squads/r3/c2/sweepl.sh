#!/bin/bash
# usage: sweepl.sh TAG STRIDE -- GROUP...   (indices 0..|Q|-1 step STRIDE; upper bound from env QMAX)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c2
TAG=$1; ST=$2; shift 2
for I in $(seq 0 $ST $((QMAX-1))); do
  ALPHA=$I ORBIT="3 3 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 10 5 1 1 8 /dev/null "$@" > sw_${TAG}_$I.log 2>&1
  f=$(grep -o '|Fix(alpha)| = [0-9]*' sw_${TAG}_$I.log | grep -o '[0-9]*$')
  m=$(grep -o 'min=[0-9]*' sw_${TAG}_$I.log | head -1 | grep -o '[0-9]*$')
  echo "$I Fix=$f min=$m"
  rm -f sw_${TAG}_$I.log
done
