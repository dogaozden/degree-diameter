#!/bin/bash
# detached finisher for card c2: waits for the polish chain, assembles best_pts/best_lines, appends the one scoreboard line
cd /home/user/degree-diameter/research/squads/d16D7_r3/c2
while [ ! -f chain_p.done ]; do sleep 10; done
./assemble.sh > assemble.out 2>&1
python3 finish_row.py > finish.log 2>&1
echo done > finish.done
