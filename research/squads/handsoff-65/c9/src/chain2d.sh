#!/bin/sh
# after the running F_L15 scan python process: long runs on the best rows so far, then the 3+3 scan (E_L14)
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while pgrep -f "scan_vl.py F_L15" >/dev/null; do sleep 10; done
python3 -I src/longrun.py 6 180 1
python3 -I src/scan_vl.py E_L14 base_L14.base 115,116,117,118,119,120 12 60000 1
