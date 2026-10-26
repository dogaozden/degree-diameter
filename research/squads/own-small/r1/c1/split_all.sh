#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/r1/c1/groups
for f in t*.txt; do [ "$f" = t136.txt ] && continue; python3 /home/user/degree-diameter/research/squads/own-small/tools/split_groups.py $f . ; done
echo SPLIT_DONE
