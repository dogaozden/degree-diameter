#!/bin/bash
# A5 screen: k = 10 outer involution (AFROBD=1), RANDORB=150 for AFROB = 1..4, one gated run at a time.
G=/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh
H=/home/user/degree-diameter/research/structured/haar_sym
A=/home/user/degree-diameter/research/squads/d11D10-r2/A5
cd "$A" || exit 1
for j in 1 2 3 4; do
  echo "start frob$j $(date -u +%T)" >> "$A/screen_status.txt"
  "$G" 240 env ORBIT="10 1 1" AFROB=$j AFROBD=1 AR=2 RANDORB=150 "$H" 11 10 60 5 8 /dev/null psl 243 11 > "$A/randorb_frob${j}_d.log" 2>&1
  echo "done frob$j rc=$? $(date -u +%T)" >> "$A/screen_status.txt"
done
echo "ALLDONE $(date -u +%T)" >> "$A/screen_status.txt"
