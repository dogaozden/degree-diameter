#!/bin/bash
# exhaustive Haar scan over metacyclic groups Z_M x|_R Z_K of order N in [LO, HI]
LO=$1; HI=$2; shift 2
for N in $(seq $LO $HI); do
  for K in $(seq 2 $N); do
    [ $((N % K)) -eq 0 ] || continue; M=$((N / K)); [ $M -ge 3 ] || continue
    for R in $(seq 2 $((M - 1))); do
      # R^K == 1 mod M and gcd(R, M) = 1
      python3 -c "import math,sys; M,K,R=$M,$K,$R; sys.exit(0 if math.gcd(R,M)==1 and pow(R,K,M)==1 else 1)" || continue
      f=tables/meta_${M}_${K}_${R}.txt
      [ -f $f ] || python3 ../groups.py "meta $M $K $R" $f > /dev/null 2>&1 || continue
      for p in "$@"; do echo "meta $M $K $R n=$N $(basename $p) $(./exh_k1r $f $p 2 | tail -3 | tr '\n' ' ')"; done
    done
  done
done
