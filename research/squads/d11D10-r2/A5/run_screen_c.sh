#!/bin/bash
# A5 screen, third waiter: AFROB=4 starts when chain a has finished AFROB=2 (keeps at most two of my gated runs at a time).
G=/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh
H=/home/user/degree-diameter/research/structured/haar_sym
A=/home/user/degree-diameter/research/squads/d11D10-r2/A5
cd "$A" || exit 1
until grep -q "done frob2" "$A/screen_status.txt"; do sleep 5; done
echo "start frob4 $(date -u +%T) (chain c)" >> "$A/screen_status.txt"
"$G" 240 env ORBIT="10 1 1" AFROB=4 AFROBD=1 AR=2 RANDORB=150 "$H" 11 10 60 5 8 /dev/null psl 243 11 > "$A/randorb_frob4_d.log" 2>&1
echo "done frob4 rc=$? $(date -u +%T) (chain c)" >> "$A/screen_status.txt"
echo "CHAINC_DONE $(date -u +%T)" >> "$A/screen_status.txt"
