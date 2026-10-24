#!/bin/bash
# A8: independent check of the k = 11 solution (run through gate.sh only if the anneal wrote a file).
A8=/home/user/degree-diameter/research/squads/d11D10-r1/A8
F="$A8/d11D10_psl_23_12409_orb11_A8_s1.txt"
[ -f "$F" ] || { echo "no solution file"; exit 1; }
/home/user/degree-diameter/research/structured/tools/haarcheck_psl "$F"
