#!/bin/bash
# alpha sweep on prod psl 3 psl 7 8, k=2 m=3 f=0, RANDORB=3000
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
cd /home/user/degree-diameter/research/squads/r3/c6
for I in $(seq 0 2015); do
  out=$(ALPHA=$I ORBIT="2 3 0" RANDORB=3000 timeout 60 nice -n 10 $B/haar_sym 6 8 1 1 8 /dev/null prod psl 3 psl 7 8 2>&1)
  fix=$(echo "$out" | grep -o 'Fix(alpha)| = [0-9]*' | grep -o '[0-9]*$')
  mu=$(echo "$out" | grep -o 'mu = [0-9.]*' | head -1 | grep -o '[0-9.]*$')
  rr=$(echo "$out" | grep '^RANDORB d=')
  if [ -z "$rr" ]; then continue; fi
  mn=$(echo "$rr" | grep -o 'min=[0-9]*' | grep -o '[0-9]*$')
  p1=$(echo "$rr" | grep -o 'p1=[0-9]*' | grep -o '[0-9]*$')
  p10=$(echo "$rr" | grep -o 'p10=[0-9]*' | grep -o '[0-9]*$')
  med=$(echo "$rr" | grep -o 'median=[0-9]*' | grep -o '[0-9]*$')
  c0=$(echo "$out" | grep -o 'cost0=[0-9]*' | grep -o '[0-9]*$')
  echo "$I fix=$fix mu=$mu min=$mn p1=$p1 p10=$p10 median=$med cost0=$c0"
done
echo DONE
