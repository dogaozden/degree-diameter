#!/bin/bash
# verify.sh VOLTAGES M : build the lifteval base graph of a q=7 design (mkbase7.py) and run the exact independent
# checker on all 19608 sources (lifteval all, m <= 64). Prints the COST line; COST 0 means diameter <= 8.
set -e
D=/home/user/degree-diameter/research/squads/r2_d14D8/c5
cd "$D"
python3 mkbase7.py "$1" "$2" "base_m$2.txt"
timeout 900 nice -n 10 /home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval "base_m$2.txt" 8 all
