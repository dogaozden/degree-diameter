#!/bin/bash
# e14: SL(2,37) x Z_397 at (6,13), N = 20094552 (mu 5.1), same N range as the metacyclic test
cd /home/user/degree-diameter/research/squads/beyond13/r2/e14
export THREADS=1
echo "== random S (10 samples)"
RANDSAMPLE=10 timeout 900 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/bin/haar_sym 6 13 30 1 8 /dev/null sl 37 397
echo "== ORBIT 3 2 0 (10 symmetric S)"
RANDORB=10 ORBIT="3 2 0" timeout 900 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/bin/haar_sym 6 13 30 1 8 /dev/null sl 37 397
echo DONE
