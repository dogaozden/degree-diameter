#!/bin/sh
# record-shaped metacyclic groups Z_pq x| Z_k (different action orders on the two primes, mostly with a central
# involution, like Loz's (4,8) group Z91 x| Z12): (4,8) just above 1092, then (4,9) just above 2485
cd "$(dirname "$0")/.."
nice -n 5 python3 named.py 4 8 "Meta(93,12,5)" "Meta(93,12,68)" "Meta(111,12,47)" "Meta(119,12,16)" \
  "DirectProduct(Meta(31,5,2), SmallGroup(8,4))" "DirectProduct(Meta(11,2,10), Meta(13,4,12))" \
  --threads 1 --outdir runs/recordshape > runs/recordshape_d4D8.log 2>&1
nice -n 5 python3 named.py 4 9 "Meta(209,12,197)" "Meta(217,12,30)" "Meta(217,12,160)" "Meta(115,22,94)" \
  "Meta(143,20,25)" "Meta(247,12,64)" "Meta(259,12,184)" --threads 1 --outdir runs/recordshape > runs/recordshape_d4D9.log 2>&1
