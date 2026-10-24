#!/bin/bash
# squad r2 c4: k=2 orbit (2 3 1) anneals on the top screened groups for (7,8), 600 s each, one at a time.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r2/c4
cd $C
run() { # tag, group spec...
  tag=$1; shift
  ORBIT="2 3 1" timeout 900 nice -n 10 $B/haar_sym 7 8 600 1 8 $C/d7D8_${tag}_orb2_s1.txt "$@" > $C/d7D8_${tag}_orb2_s1.log 2>&1
  echo "EXIT $?" >> $C/d7D8_${tag}_orb2_s1.log
}
run psl23x8 psl 23 8
run sl29x2 sl 29 2
run sl23x4 sl 23 4
echo DONE > $C/anneal_231.done
