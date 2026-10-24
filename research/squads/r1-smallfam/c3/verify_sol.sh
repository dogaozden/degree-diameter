#!/bin/bash
# usage: verify_sol.sh SMALLFAM_EXPR D OUTNAME i1 i2 i3 i4   (indices from a SOL line; Delta = 4)
# Rebuilds the Haar graph edge list with GAP (named_edges.py) and checks it with all-pairs BFS (verify/apsp).
set -e
SF=/home/user/degree-diameter/research/theorems/smallfam
EXPR="$1"; D="$2"; OUT="/home/user/degree-diameter/research/squads/r1-smallfam/c3/$3"; shift 3
cd "$SF"
python3 named_edges.py "$EXPR" "$OUT.edges" "$@"
./verify/apsp "$OUT.edges" 4 "$D" | tail -n 5
