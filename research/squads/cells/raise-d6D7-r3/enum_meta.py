"""Enumerate metacyclic groups G = Z_m x|_r Z_K (order m*K in [LO, HI]) with an automorphism alpha(a,j)=(u a, j)
of order k (k in KS) and few fixed points, for the orbit screen of (6,7) round 3.
One r per cyclic subgroup of Z_m^* (r^K = 1, r != 1); one u per k with gcd(u-1,m) minimal.
usage: enum_meta.py LO HI > jobs_meta.txt   (lines:  ORBIT | - | meta m K r 1)"""
import sys
from math import gcd
LO, HI = int(sys.argv[1]), int(sys.argv[2])
KS = {2: '2 3 0', 3: '3 2 0', 4: '4 1 2', 5: '5 1 1', 6: '6 1 0'}
MAXG = 3          # largest gcd(u-1, m) allowed: Fix(alpha) = K * gcd(u-1, m) stays small
out = []
for K in range(2, 61):
    for m in range((LO + K - 1) // K, HI // K + 1):
        if m < 3: continue
        units = [x for x in range(2, m) if gcd(x, m) == 1]
        if not units: continue
        seen, reps = set(), []
        for r in units:
            if pow(r, K, m) != 1: continue
            sub = frozenset(pow(r, i, m) for i in range(K))
            if len(sub) == 1 or sub in seen: continue
            seen.add(sub); reps.append(r)
        if not reps: continue
        # order of each unit, and the best fixed-point gcd per k
        ordr = {}
        best_u = {}
        for u in units:
            o, y = 1, u
            while y != 1:
                y = y * u % m; o += 1
                if o > 60: break
            if o > 60 or o not in (2, 3, 4, 5, 6): continue
            g = gcd(u - 1, m)
            if g > MAXG: continue
            if o not in best_u or g < best_u[o][1]: best_u[o] = (u, g)
        for k, orb in KS.items():
            if k not in best_u: continue
            if k in (2, 3, 4, 5, 6) and k not in best_u: continue
            for r in reps:
                out.append('%s | - | meta %d %d %d 1  # Fix=%d' % (orb, m, K, r, K * best_u[k][1]))
print('\n'.join(out))
