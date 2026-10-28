#!/bin/bash
# usage: mkgen.sh q m z0 z1 z2 z3 z4 z5  -> prints generator lines "a b c d z" (PGL(2,q) x Z_m, base LPS(5,q))
q=$1; m=$2; shift 2
paste -d' ' <(awk '{print $1,$2,$3,$4}' /home/user/degree-diameter/research/squads/thmfam-r2/c4/base$q.txt) <(printf "%s\n" "$@")
