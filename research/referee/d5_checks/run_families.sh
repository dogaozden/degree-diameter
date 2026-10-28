#!/bin/sh
# explicit families of sec. 10 / sec. 14 "theorem family" column, built by families.py, checked by bfs.c
S=${1:-/tmp}
set -e
run() { python3 families.py "$@"; ./bfs 5 < "$7"; rm -f "$7"; }
run 10.2 7 2 22 22 Y1:3 $S/fam.edges 1                 # (10,5) 4,044
run 10.1 8 2 120 120 Y3:3:1 $S/fam.edges 2             # (11,5) 6,090
run 10.1 8 3 120 120 Y3:3:1 $S/fam.edges 3             # (12,5) 8,430
run 10.3 9 3 42 30 Y1:4 $S/fam.edges 4                 # (13,5) 11,552
run 10.4 9 4 26 26 Y1:3 $S/fam.edges 5                 # (14,5) 14,812
run 10.3 11 3 66 36 Y1:5 $S/fam.edges 6                # (15,5) 20,598
run 10.4 11 4 63 38 Y1:4 $S/fam.edges 7                # (16,5) 26,453 (below the table)
run 10.2 7 2 22 22 Y1:3 $S/fam.edges 8                 # (10,5) again, other random choices

echo "negative control: Cor 10.2, q=7, one extra line meeting a line of the set on the D->H arcs"
python3 families.py 10.2 7 2 22 22 Y1:3 $S/fam.edges 1 plus1; ./bfs 5 < $S/fam.edges
