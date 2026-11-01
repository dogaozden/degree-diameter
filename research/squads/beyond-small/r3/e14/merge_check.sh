#!/bin/sh
# usage: merge_check.sh ORB_B_FILE TAG  -- merges the 27 A-orbits of r3/orbAB_27_21.txt with ORB_B_FILE, builds, checks
set -e
cd /home/user/degree-diameter/research/squads/beyond-small/r3/e14
head -n 27 ../orbAB_27_21.txt > merged_$2.txt
cat "$1" >> merged_$2.txt
nb=$(wc -l < "$1")
python3 build_orbits.py merged_$2.txt g_$2.edges
timeout 100 nice -n 10 ../../bin/apsp g_$2.edges 17 5 | tail -n 2
echo "B-orbits: $nb"
