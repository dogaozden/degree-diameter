#!/bin/sh
# final_check.sh design.txt k q out_base.txt : expand a quotient design to the full base graph and run the exact checker
set -e
HERE=/home/user/degree-diameter/research/squads/r2_d14D8/c1
python3 "$HERE/mkbase.py" "$1" "$2" "$HERE/$4" "$3"
timeout 900 nice -n 10 /home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval "$HERE/$4" 8 all
