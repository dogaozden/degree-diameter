#!/bin/bash
cd /home/user/degree-diameter/research/squads/thmfam-r2/c5
while pgrep -f "sweep_cyc.py 7 11 8 153" > /dev/null; do sleep 5; done
nice -n 10 python3 sweep_cyc.py 7 11 8 169,181 > sweep_b2a.log 2>&1
nice -n 10 python3 sweep_cyc.py 7 31 8 7 > sweep_b2b.log 2>&1
nice -n 10 python3 sweep_cyc.py 7 19 8 31,37,39 > sweep_b2c.log 2>&1
nice -n 10 python3 sweep_cyc.py 7 23 8 19,21,31 > sweep_b2d.log 2>&1
nice -n 10 python3 sweep_cyc.py 7 13 8 93,97,103,109,111 > sweep_b2e.log 2>&1
nice -n 10 python3 sweep_cyc.py 7 17 8 43,57,61,67 > sweep_b2f.log 2>&1
echo done > batch2.done
