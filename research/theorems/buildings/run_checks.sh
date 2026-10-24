#!/bin/bash
# Independent all-pairs checks (research/lifts/coordinator_check/apsp.c, no symmetry assumed) of flag graphs built
# by polar_flags.py, and of Delorme products / quotients built by delorme.py.  Edge files go to $TMPD.
# usage: bash run_checks.sh TMPDIR APSP_BINARY   (output: out/apsp_checks.txt)
TMPD=$1; APSP=$2; cd "$(dirname "$0")"; mkdir -p "$TMPD"
run() {  # name, polar_flags args, max degree, D
  python3 polar_flags.py $2 "$TMPD/$1.edges" > /dev/null
  echo "== flag graph $1 ($2): apsp $3 $4"; timeout 3000 "$APSP" "$TMPD/$1.edges" $3 $4
}
prod() { # name, polar_flags args, product degree, D, quotient degree, D-1
  python3 polar_flags.py $2 "$TMPD/$1.edges" > /dev/null
  python3 delorme.py "$TMPD/$1.edges" "$TMPD/$1.prod.edges" "$TMPD/$1.quot.edges" 2> "$TMPD/$1.log"
  echo "== Delorme product of $1 ($2): $(cat $TMPD/$1.log | head -1)"; timeout 3000 "$APSP" "$TMPD/$1.prod.edges" $3 $4
  echo "== Delorme quotient of $1 (general graph; apsp prints its diameter; bipartite=no expected)"
  timeout 3000 "$APSP" "$TMPD/$1.quot.edges" $5 $6
}
run A3q3 "PG 3 3" 16 4
run C3q3 "Sp 3 3" 16 6
run B3q3 "O 3 3" 16 6
run C2q3_9 "Om 2 3" 10 4
run C3q2_4 "Om 3 2" 15 6
run C2q4_8 "U 5 4" 9 4
run C3q4_2 "U 6 4" 15 6
run D4q2 "Op 4 2" 27 6
run A5q2 "PG 5 2" 27 6
prod A2q3 "PG 2 3" 16 3 16 2
prod C2q2 "Sp 2 2" 9 4 9 3
prod C2q2_4 "Om 2 2" 15 4 15 3
prod A3q2 "PG 3 2" 27 4 27 3
prod C2q3_9 "Om 2 3" 40 4 40 3
prod C2q4_8 "U 5 4" 45 4 45 3
