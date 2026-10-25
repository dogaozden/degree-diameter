#!/bin/bash
# B3 merged job: length-7 identity check, then ball-size levels, then plain-random baseline (one gate slot)
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
bash run_ident7.sh
bash run_levels.sh > levels.log 2>&1
bash run_random40.sh > random40.log 2>&1
echo "=== all B3 jobs done ===" >> random40.log
