#!/bin/sh
# one heavy process at a time: sequential scans
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
python3 -I src/scan_vl.py A_L13 base_L13.base 58,59,60 20 90000 1
python3 -I src/scan_vl.py B_L7 base_L7.base 58,59,60 20 90000 1
python3 -I src/scan_vl.py C_L5 base_L5.base 20,21,22 20 90000 1
python3 -I src/scan_vl.py D_L6 base_L6.base 39,40,42 20 90000 1
