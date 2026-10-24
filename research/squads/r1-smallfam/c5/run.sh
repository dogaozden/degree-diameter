#!/bin/bash
cd /home/user/degree-diameter/research/theorems/smallfam
export THREADS=1
timeout 900 nice -n 10 python3 named.py 4 8 "SmallGroup(1094,1)" "SmallGroup(1102,3)" "SmallGroup(1106,3)" "SmallGroup(1114,1)" "SmallGroup(1118,3)" "SmallGroup(1126,1)" "SmallGroup(1130,3)" "SmallGroup(1138,1)" "SmallGroup(1101,1)" "SmallGroup(1119,1)" "SmallGroup(1137,1)" "SmallGroup(1108,1)" "SmallGroup(1108,3)" "SmallGroup(1108,4)" "SmallGroup(1124,1)" "SmallGroup(1124,3)" "SmallGroup(1124,4)" "SmallGroup(1132,1)" "SmallGroup(1132,3)" "SmallGroup(1130,2)" "SmallGroup(1106,2)" "SmallGroup(1095,1)" --threads 1 --outdir /home/user/degree-diameter/research/squads/r1-smallfam/c5
