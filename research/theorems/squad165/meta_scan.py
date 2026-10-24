"""Exhaustive Haar-controller scan (ctrl_exh) over all metacyclic groups Z_a x|_r Z_b of each order m in [lo, hi]."""
import subprocess, sys, os
from math import gcd
import controller as ct
lo, hi = int(sys.argv[1]), int(sys.argv[2])
tmp = os.environ.get('TMPD', '/tmp/claude-0')
for m in range(lo, hi + 1):
    best = None
    for a in range(1, m + 1):
        if m % a: continue
        b = m // a
        seen = set()
        for r in range(1, max(a, 2)):
            if a > 1 and (gcd(r, a) != 1 or pow(r, b, a) != 1 % a): continue
            orbit = frozenset(pow(r, k, a) if a > 1 else 0 for k in range(1, b + 1) if gcd(k, b) == 1)
            if orbit in seen: continue
            seen.add(orbit)
            T = ct.meta(a, b, r)
            fn = f'{tmp}/t_{m}_{os.getpid()}.txt'
            with open(fn, 'w') as f:
                f.write(f"{m}\n" + ' '.join(map(str, T.flatten().tolist())) + '\n')
            out = subprocess.run(['./ctrl_exh', fn, '1'], capture_output=True, text=True).stdout.strip().splitlines()
            last = out[-1]
            bc = int(last.split('best_cost=')[1].split()[0]); ns = int(last.split('solutions=')[1].split()[0])
            key = (bc, -ns)
            if best is None or key < best[0]:
                best = (key, f'meta {a} {b} {r}', out[0] if ns else '')
    print(m, best, flush=True)
