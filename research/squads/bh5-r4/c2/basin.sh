#!/bin/bash
# basin runs on the two best screen groups (g2, g9), sequential, 12 runs x 40 s each
cd /home/user/degree-diameter/research/beyond-haar-d5
G=/home/user/degree-diameter/research/squads/bh5-r4/c2
timeout 1000 nice -n 10 basin/run2.sh b6/b33_9.txt $G/groups/sg_60_2.txt b6_9_g2_r4 1 12 40 6 4
timeout 1000 nice -n 10 basin/run2.sh b6/b33_9.txt $G/groups/sg_60_9.txt b6_9_g9_r4 1 12 40 6 4
