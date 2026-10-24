#!/bin/bash
# Independent all-pairs check (apsp.c) of the remaining flag graphs of compare_dist.py (the other nine are in
# run_checks.sh).  usage: bash run_checks2.sh TMPDIR APSP_BINARY  (output: out/apsp_checks2.txt)
TMPD=$1; APSP=$2; cd "$(dirname "$0")"; mkdir -p "$TMPD"
run() { python3 polar_flags.py $2 "$TMPD/$1.edges" > /dev/null
        echo "== flag graph $1 ($2): apsp $3 $4"; timeout 5000 "$APSP" "$TMPD/$1.edges" $3 $4; }
run A2q2 "PG 2 2" 3 3
run A2q3 "PG 2 3" 4 3
run A3q2 "PG 3 2" 9 4
run A4q2 "PG 4 2" 9 5
run C2q2 "Sp 2 2" 3 4
run C2q3 "Sp 2 3" 4 4
run B2q3 "O 2 3" 4 4
run C3q2 "Sp 3 2" 9 6
run C2q2_4 "Om 2 2" 5 4
run C2q4_2 "U 4 4" 5 4
run A4q3 "PG 4 3" 16 5
run C4q2 "Sp 4 2" 9 8
