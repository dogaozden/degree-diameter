#!/bin/bash
# correction: the screen's second-best group is g1 (cost 16); g9 (cost 17) was basin-run by mistake. 8 runs x 40 s.
cd /home/user/degree-diameter/research/beyond-haar-d5
G=/home/user/degree-diameter/research/squads/bh5-r4/c2
timeout 600 nice -n 10 basin/run2.sh b6/b33_9.txt $G/groups/sg_60_1.txt b6_9_g1_r4 1 8 40 6 4
