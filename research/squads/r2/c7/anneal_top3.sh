#!/bin/bash
# Anneal the top 3 screened groups (k=2, ORBIT="2 3 1"), 600 s each, seed 1, sequentially.
cd /home/user/degree-diameter/research/squads/r2/c7
run() { # tag, group spec...
  tag=$1; shift
  ORBIT="2 3 1" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 7 9 600 1 8 /home/user/degree-diameter/research/squads/r2/c7/d7D9_${tag}_orb2_s1.txt "$@" > /home/user/degree-diameter/research/squads/r2/c7/d7D9_${tag}_orb2_s1.log 2>&1
}
run prod_psl_3_sl_27_1 prod psl 3 sl 27 1
run sl_31_8 sl 31 8
run psl_31_16 psl 31 16
echo ALLDONE
