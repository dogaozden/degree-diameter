#!/bin/bash
# prints LABEL|GAP_EXPR|h for direct products T x C_k with admissible subgroup order h (n = 2|G|/h in 686..800, h>=4)
while IFS='|' read -r tname texpr tord; do
  for k in $(seq 2 40); do
    m=$((tord*k))
    for h in $(seq 4 $m); do
      if [ $((m % h)) -eq 0 ]; then
        n=$((2*m/h))
        if [ $n -ge 686 ] && [ $n -le 800 ]; then
          echo "P_${tname}x${k}|DirectProduct(${texpr}, CyclicGroup(IsPermGroup, ${k}))|$h"
        fi
      fi
    done
  done
done <<'LIST'
A5|AlternatingGroup(5)|60
S5|SymmetricGroup(5)|120
PSL27|PSL(2,7)|168
PGL27|PGL(2,7)|336
A6|AlternatingGroup(6)|360
PSL28|PSL(2,8)|504
S6|SymmetricGroup(6)|720
PSL211|PSL(2,11)|660
PSL213|PSL(2,13)|1092
PSL217|PSL(2,17)|2448
S4|SymmetricGroup(4)|24
PSL219|PSL(2,19)|3420
A4|AlternatingGroup(4)|12
LIST
