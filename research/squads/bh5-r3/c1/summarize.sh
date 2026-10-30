#!/bin/bash
# c1: per-order summary of the (7,5) h=3 sweep (reads coset/logs/sweep_h3_d7.txt; orders 1731..1845 step 3)
F=/home/user/degree-diameter/research/beyond-haar-d5/coset/logs/sweep_h3_d7.txt
awk '
/^RESULT/ {
  f=$2; sub(/^tmp_/,"",f); split(f,p,"/"); o=p[1]; sub(/_3$/,"",o); sub(/^sg/,"",o); split(o,q,"_"); ord=q[1];
  tested=$4; sols=$6; best=$8; vert=$10;
  n[ord]++; T[ord]+=tested; S[ord]+=sols; if (!(ord in B) || best+0 < B[ord]+0) B[ord]=best; V[ord]=vert;
  if (tested>=2000000) cap[ord]++;
}
END { for (o in n) printf "order %s pairs_done %d tested %d solutions %d best_cost %s vertices %s capped_pairs %d\n", o, n[o], T[o], S[o], B[o], V[o], cap[o]+0 }' "$F" | sort -n
