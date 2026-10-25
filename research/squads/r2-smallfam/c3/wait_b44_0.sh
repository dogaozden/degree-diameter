#!/bin/bash
# wait until b44_0 has finished or the 04:57:30 cutoff, then stop the screen
cd /home/user/degree-diameter/research/squads/r2-smallfam/c3
end=$(date -d "04:57:30" +%s)
until grep -q "== end b44_0" screen.log || [ "$(date +%s)" -ge "$end" ]; do sleep 3; done
./stop_screen.sh
cat screen.log
