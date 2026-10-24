#!/bin/bash
# squad r2 c4: compare ORBIT="2 2 3" on the best group (psl 23 x Z8) after the (2 3 1) chain finishes; 300 s.
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r2/c4
cd $C
until [ -f $C/anneal_231.done ]; do sleep 5; done
ORBIT="2 2 3" timeout 900 nice -n 10 $B/haar_sym 7 8 300 1 8 $C/d7D8_psl23x8_orb2_223_s1.txt psl 23 8 > $C/d7D8_psl23x8_orb2_223_s1.log 2>&1
echo "EXIT $?" >> $C/d7D8_psl23x8_orb2_223_s1.log
echo DONE > $C/cmp_223.done
