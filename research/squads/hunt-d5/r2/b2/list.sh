#!/bin/bash
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b2
for N in $(seq 606 660); do timeout 300 nice -n 10 python3 ../../tools/gapgroup.py list $N >> all_groups.txt 2>/dev/null || echo "FAIL $N" >> list_fail.txt; done
echo LISTDONE >> list_fail.txt
