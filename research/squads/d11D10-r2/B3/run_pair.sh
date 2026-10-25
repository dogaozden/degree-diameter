#!/bin/bash
# B3: per-generator coincidences of walks (length <= 5) split by whether a walk contains an h-pair adjacency (sigma, phi sigma)
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
for s in 1 2 3; do python3 ident_pair.py k10 1 5 $s; done
python3 ident_pair.py k5 1 5 1
echo "=== done pair ==="
