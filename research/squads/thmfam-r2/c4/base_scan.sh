#!/bin/bash
# base LPS(5,q) (m=1): diameter and component size for primes q
H=/home/user/degree-diameter/research/theorems/haar_families
for q in 7 11 13 17 19 23 29 31 37 41 43 47 53; do
  python3 $H/gen_lps_cover.py 5 $q 1 zero 2>/dev/null | nice -n 10 timeout 900 $H/haar_ecc pgl $q 1
done
