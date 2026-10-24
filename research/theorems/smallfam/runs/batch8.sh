#!/bin/sh
# (4,8): metacyclic groups with a central involution and products with dicyclic factors, just above 1092 (the record
# group is SmallGroup(1092,4) = (C7:C3) x Dic13 = Z91 x| Z12 with r of order 6)
cd "$(dirname "$0")/.."
nice -n 5 python3 named.py 4 8 "Meta(55,20,14)" "Meta(95,12,64)" "Meta(95,12,84)" "Meta(143,8,109)" "Meta(183,6,74)" \
  "DirectProduct(Meta(7,6,3), Meta(7,4,6))" "DirectProduct(Aff(1,8,Group([[Z(8)]])), Meta(5,4,4))" \
  "Meta(217,6,191)" "Meta(217,6,149)" --threads 1 --outdir runs/centralinv_d4D8 > runs/centralinv_d4D8.log 2>&1
