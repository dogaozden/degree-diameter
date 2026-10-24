#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c2
while read N n name; do
  tag=$(echo "$name $n" | tr ' ' '_')
  ORBIT="3 3 1" RANDORB=20000 timeout 120 nice -n 10 $B/haar_sym 10 5 1 1 8 /dev/null prod $name $n > s1_$tag.log 2>&1
  fixl=$(grep -o '|Fix(alpha)| = [0-9]*' s1_$tag.log | grep -o '[0-9]*$')
  mu=$(grep -o 'mu = [0-9.]*' s1_$tag.log | head -1 | grep -o '[0-9.]*$')
  mn=$(grep -o 'min=[0-9]*' s1_$tag.log | head -1)
  p1=$(grep -o 'p1=[0-9]*' s1_$tag.log | head -1)
  al=$(grep -o 'index [0-9]*' s1_$tag.log | head -1)
  rej=$(grep -i 'bad\|error\|no conj\|no element\|not an auto\|out of range\|alpha' s1_$tag.log | grep -v 'alpha: conj' | head -1)
  echo "$N $name x Z$n | Fix=$fixl mu=$mu $mn $p1 $al | $rej"
done < cands_run.txt
