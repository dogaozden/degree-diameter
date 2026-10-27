#!/bin/bash
# scan LPS Haar graphs: p in $1, primes q in [3, $2]
p=$1; Q=$2
for q in $(python3 -c "
Q=$Q; p=$p
pr=[x for x in range(3,Q+1) if all(x%d for d in range(2,int(x**.5)+1))]
print(' '.join(str(x) for x in pr if x!=p and x>p))"); do
  timeout 600 nice -n 10 ./lps_haar $p $q
done
