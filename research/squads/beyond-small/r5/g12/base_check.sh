#!/bin/bash
cd "$(dirname "$0")"
B=/home/user/degree-diameter/research/squads/beyond-small
python3 $B/graphs/build_d17D5_hubs.py base_check.edges --orbits startA.txt --orbits startB.txt > base_check.log 2>&1
$B/bin/apsp base_check.edges 17 5 >> base_check.log 2>&1
echo BASEDONE >> base_check.log
