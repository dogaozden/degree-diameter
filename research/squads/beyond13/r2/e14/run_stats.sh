#!/bin/bash
# e14: first-eval cost statistics at (6,13), odd-order metacyclic Z_1079011 x|_305965 Z_19 (N = 20501209)
cd /home/user/degree-diameter/research/squads/beyond13/r2/e14
export THREADS=1
echo "== ORBIT 3 2 0 (10 random symmetric S)"
RANDORB=10 ORBIT="3 2 0" timeout 600 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/bin/haar_sym 6 13 30 1 8 /dev/null meta 1079011 19 305965 1
echo "== random S haar_sym RANDSAMPLE (10 samples)"
RANDSAMPLE=10 timeout 600 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/bin/haar_sym 6 13 30 1 8 /dev/null meta 1079011 19 305965 1
echo DONE
