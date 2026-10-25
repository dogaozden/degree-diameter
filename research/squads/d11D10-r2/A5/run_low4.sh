#!/bin/bash
# A5: rerun of the AFROB=4 AFROBD=1 RANDORB=150 screen (seed 5) with the patched copy; prints generators of samples with cost <= 25.
G=/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh
A=/home/user/degree-diameter/research/squads/d11D10-r2/A5
cd "$A" || exit 1
echo "start low4 $(date -u +%T)" >> "$A/screen_status.txt"
"$G" 240 env SHOWLOW=25 ORBIT="10 1 1" AFROB=4 AFROBD=1 AR=2 RANDORB=150 "$A/haar_sym_A5" 11 10 60 5 8 /dev/null psl 243 11 > "$A/randorb_frob4_low_d.log" 2>&1
echo "done low4 rc=$? $(date -u +%T)" >> "$A/screen_status.txt"
