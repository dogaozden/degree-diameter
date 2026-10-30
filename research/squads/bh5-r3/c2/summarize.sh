#!/bin/bash
# c2 summary: best cost per (order, h) from the shared coset logs, restricted to this card's orders
L=/home/user/degree-diameter/research/beyond-haar-d5/coset/logs
for h in 3 4; do
  f=$L/sweep_h${h}_d5.txt; [ -f "$f" ] || continue
  for o in 534 537 540 543 549 552 555 558 712 716 720 724 728 732 736 740 744; do
    grep -E "tmp_${o}_${h}/" "$f" 2>/dev/null | awk -v o=$o -v h=$h '
      { n++; for(i=1;i<=NF;i++){ if($i=="best") b=$(i+1); if($i=="solutions") s=$(i+1); if($i=="tested") t=$(i+1) }
        if(n==1||b<best) best=b; sols+=s; tested+=t }
      END { if(n>0) printf "order %d h %d files %d tested %d best %d solutions %d\n", o, h, n, tested, best, sols }'
  done
done
