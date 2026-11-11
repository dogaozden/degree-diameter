#!/bin/bash
# (4,7) above the table (840): Haar graphs (dipole, 4 parallel edges) over matrix-group products. 60 s per seed.
cd "$(dirname "$0")/.."
while read -r N G; do
  for s in 1 2; do
    r=$(./lift search bases/dipole4.txt 7 60 $s 4 sols/d4D7_haar_N${N}_$(echo $G | tr -d ' ')_s$s.txt $G 2>/dev/null | grep RESULT)
    echo "$N | $G | s$s | $r"
  done
done <<'LIST'
432 sl 3 x cyc 18
432 pgl 3 x cyc 18
432 psl 3 x cyc 36
456 sl 3 x cyc 19
456 pgl 3 x cyc 19
480 psl 5 x cyc 8
480 psl 5 x cyc 2 x cyc 4
480 psl 5 x dih 4
480 sl 5 x cyc 4
480 pgl 5 x cyc 4
480 sl 3 x cyc 20
504 psl 7 x cyc 3
504 sl 3 x cyc 21
504 sl 3 x meta 7 3 2
540 psl 5 x cyc 9
540 psl 5 x cyc 3 x cyc 3
LIST
