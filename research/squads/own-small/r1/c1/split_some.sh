#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/r1/c1/groups
for N in 134 135 138 140 142 146 147 148 150 152 154 155 156 158 164 165 166 170 162 168 144 160; do python3 /home/user/degree-diameter/research/squads/own-small/tools/split_groups.py t$N.txt . ; echo "split $N"; done
echo SPLIT_DONE
