#!/bin/sh
# runs after chain1: 3+3 base (C114 quotient) by orders 115..120, then 6+6 bases by orders 61..66 (no 64)
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while pgrep -f chain1.sh >/dev/null; do sleep 10; done
python3 -I src/scan_vl.py E_L14 base_L14.base 115,116,117,118,119,120 20 90000 1
python3 -I src/scan_vl.py A2_L13 base_L13.base 61,62,63,65,66 20 90000 1
python3 -I src/scan_vl.py B2_L7 base_L7.base 61,62,63,65,66 20 90000 1
