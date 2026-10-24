#!/bin/bash
# usage: sweep.sh TAG LO HI  (GROUP args from SWEEP_GROUP env, ncyc last token)
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c2
TAG=$1; LO=$2; HI=$3; shift 3
for I in $(seq $LO $HI); do
  ALPHA=$I ORBIT="3 3 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 10 5 1 1 8 /dev/null "$@" > sw_${TAG}_$I.log 2>&1
  f=$(grep -o '|Fix(alpha)| = [0-9]*' sw_${TAG}_$I.log | grep -o '[0-9]*$')
  m=$(grep -o 'min=[0-9]*' sw_${TAG}_$I.log | head -1 | grep -o '[0-9]*')
  p=$(grep -o 'p1=[0-9]*' sw_${TAG}_$I.log | head -1 | grep -o '[0-9]*')
  e=$(grep -i 'wrong\|no conj\|out of range\|not an auto\|order' sw_${TAG}_$I.log | head -1)
  echo "$I Fix=$f min=$m p1=$p $e"
  rm -f sw_${TAG}_$I.log
done
