#!/bin/bash
cd /home/user/degree-diameter/research/squads/r1/c2
ORBIT="3 3 2" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 11 5 300 1 8 pgl312_122_s1.txt pgl 3 122 > pgl312_122_s1.log 2>&1; echo EXIT $? >> pgl312_122_s1.log
ORBIT="3 3 2" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 11 5 300 1 8 psl3247_s1.txt psl 3 247 > psl3247_s1.log 2>&1; echo EXIT $? >> psl3247_s1.log
echo DONE > chain3.done
