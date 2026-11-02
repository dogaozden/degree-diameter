#!/bin/bash
cd /home/user/degree-diameter/research/squads/deep-65b/round1/c3
for g in $(cut -d' ' -f1 out/leaf_totals_300.txt | sed 's/300_//' ); do
  n=$(ls out/ex_300_${g}_p*of8.txt 2>/dev/null | wc -l); d=$(grep -l TOTAL out/ex_300_${g}_p*of8.txt 2>/dev/null | wc -l)
  if [ "$d" -eq 8 ]; then st="complete"; else st="partial $d/8"; fi
  grep -h "done:" out/ex_300_${g}_p*of8.txt | awk -v g=$g -v st="$st" -v name="$(cut -d' ' -f1-3 tabs/sg_300_$g.name)" '
    {for(i=1;i<=NF;i++){ if($i=="leaves") L+=$(i+1); if($i=="(3)(6)") P+=$(i+1); if($i=="(2)(5)") Q+=$(i+1); if($i=="solutions") S+=$(i+1); if($i=="miss" && $(i+1)+0<B+0 ) B=$(i+1); if($i=="s") T+=$(i-1) } }
    END{ printf "300_%s | %s | leaves %d | pass(3)(6) %d | pass(2)(5) %d | solutions %d | best miss %s | chunk wall sum %.0f s | %s\n", g, name, L, P, Q, S, (B? B : "none (no leaf passes (3)(6))"), T, st }'
done
