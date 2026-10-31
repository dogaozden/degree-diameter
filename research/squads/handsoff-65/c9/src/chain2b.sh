#!/bin/sh
# after chain1: 2+2 base (L15, C3x(C19:C3) quotient) by orders 172..180, then 3+3 base (L14) by 115..120, then 6+6 bases 61-66
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while kill -0 32738 2>/dev/null; do sleep 10; done
python3 -I src/scan_vl.py F_L15 base_L15.base 172,173,174,175,176,177,178,179,180 20 90000 1
python3 -I src/scan_vl.py E_L14 base_L14.base 115,116,117,118,119,120 20 90000 1
python3 -I src/scan_vl.py A2_L13 base_L13.base 61,62,63,65,66 20 90000 1
python3 -I src/scan_vl.py B2_L7 base_L7.base 61,62,63,65,66 20 90000 1
