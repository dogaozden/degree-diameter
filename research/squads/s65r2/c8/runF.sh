#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c8
env TYPE="1|2,2" SECS=120 SEED=2 RANDCOMB=4 EDGES=edges/F_360_124.edges timeout 600 nice -n 10 /home/user/degree-diameter/research/s65/tools/mcos /home/user/degree-diameter/research/s65/groups/mc/sg_360_124.txt > logs/F_360_124.log 2>&1
env TYPE="1|2,2" SECS=120 SEED=2 RANDCOMB=4 EDGES=edges/F_360_123.edges timeout 600 nice -n 10 /home/user/degree-diameter/research/s65/tools/mcos /home/user/degree-diameter/research/s65/groups/mc/sg_360_123.txt > logs/F_360_123.log 2>&1
echo done > logs/runF.done
