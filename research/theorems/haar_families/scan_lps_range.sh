#!/bin/bash
# scan_lps_range.sh p qmin qmax : LPS Haar graphs for primes q in [qmin, qmax], q > p
p=$1
for q in $(python3 -c "
pr=[x for x in range($2,$3+1) if x>2 and all(x%d for d in range(2,int(x**.5)+1))]
print(' '.join(str(x) for x in pr if x>$p))"); do
  nice -n 10 timeout 1200 ./lps_haar $p $q | tail -n 1
done
