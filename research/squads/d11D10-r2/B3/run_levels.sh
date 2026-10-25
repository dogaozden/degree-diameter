#!/bin/bash
# B3: ball sizes per BFS level (distinct B-side elements after each step) for three generator sets on psl 243 x Z11.
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
HS=/home/user/degree-diameter/research/structured/haar_sym
echo "=== k=10 AFROB=1 AFROBH=0 1 2 0 AR=2 (one orbit, alpha order 10) ==="
env -u THREADS ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2 RANDORB=3 LEVELS=3 $HS 11 10 60 5 8 /dev/null psl 243 11
echo "=== k=5 AFROB=1 ORBIT=5 2 1 (Frobenius, z -> 3z) ==="
env -u THREADS ORBIT="5 2 1" AFROB=1 RANDORB=3 LEVELS=3 $HS 11 10 60 5 8 /dev/null psl 243 11
echo "=== plain random S ==="
env -u THREADS RANDSAMPLE=3 LEVELS=3 $HS 11 10 60 5 8 /dev/null psl 243 11
echo "=== done ==="
