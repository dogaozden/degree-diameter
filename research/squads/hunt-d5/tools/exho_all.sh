#!/bin/bash
# exho_all.sh N I d [KLIST] : exhaustive orbit-symmetric Haar search over every automorphism class of each order K
# and every orbit shape "K m f" with K*m + f = d (f >= 1 includes the identity; f = 0 allowed when K | d).
N=$1; I=$2; d=$3; KL=${4:-"2 3 4 5 6 7 8 9"}
T=../tables/g${N}_${I}.bin; mkdir -p ../tables
for K in $KL; do
  [ -f $T.aut$K ] || python3 $(dirname $0)/gapgroup.py table $N $I $T $K
  [ -s $T.aut$K ] || continue
  nl=$(wc -l < $T.aut$K)
  for ((a=0; a<nl; a++)); do
    for ((m=1; K*m<=d; m++)); do f=$((d-K*m)); [ $f -lt 0 ] && continue
      r=$(AUT=$T.aut$K ALINE=$a ORBIT="$K $m $f" timeout ${TMO:-600} $(dirname $0)/haar5 exho $T $d 0 2>/dev/null | tail -1)
      echo "N=$N I=$I K=$K alpha=$a orbit=$K,$m,$f :: $r"
    done
  done
done
