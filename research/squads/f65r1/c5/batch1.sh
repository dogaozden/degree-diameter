#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c5
for g in A5xZ3 Z31_r26 Z31_r5 Z31_rm1 SL23xZ8 S4xZ8 Z43_rm1 Z13_rm1 Z23_rm1 Z11_rm1 Z5_r2; do
 for p in 1 2 3; do
  for a in 0 1; do
   out=runs/${g}_p${p}_a${a}_m0
   r=$(timeout 120 nice -n 10 ./sym2lift grp/$g.grp grp/$g.aut$a $p 0 3 $((p*10+a)) $out 2>&1 | grep RESULT)
   echo "$g p=$p aut=$a mode=0 :: $r"
   if echo "$r" | grep -q "best_cost=0 "; then echo "FOUND $out"; fi
  done
 done
done
echo BATCH1_DONE
