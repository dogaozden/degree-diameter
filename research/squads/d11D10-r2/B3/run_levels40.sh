#!/bin/bash
# B3: ball sizes (distinct B-side counts per radius) for 40 samples each, k = 10 and k = 5 orbits, psl 243 x Z11
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
HS=/home/user/degree-diameter/research/structured/haar_sym
echo "=== k10 40 ==="
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=40 LEVELS=40 $HS 11 10 60 21 8 /dev/null psl 243 11 2>&1
echo "=== k5 40 ==="
env -u THREADS ORBIT="5 2 1" AFROB=1 RANDORB=40 LEVELS=40 $HS 11 10 60 21 8 /dev/null psl 243 11 2>&1
echo "=== done levels40 ==="
