"""Check that a frob_scan output covers every Z_p x|_r Z_k (p prime, r of order > 1 dividing gcd(k, p-1), one r per
relabelling class, as in frob_scan.actions) with N = p k in [NMIN, NMAX].  Usage: python3 frobcover.py FILE NMIN NMAX"""
import sys
from frob_scan import actions, primes_upto
fn, nmin, nmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
have = set()
for line in open(fn):
    f = line.split()
    if len(f) >= 5 and f[0].isdigit():
        have.add((int(f[0]), int(f[1]), int(f[2])))
need = set()
for p in primes_upto(nmax):
    for k in range(2, nmax // p + 1):
        if nmin <= p * k <= nmax:
            for r, k0 in actions(p, k):
                need.add((p, k, r))
missing = sorted(need - have)
print(f'{fn}: N in [{nmin},{nmax}]: {len(need)} groups needed, {len(need & have)} present, {len(missing)} missing'
      + (f'; first missing: {missing[:8]}' if missing else ''))
