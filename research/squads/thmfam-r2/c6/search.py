#!/usr/bin/env python3
"""c6: free-label search for LPS(3) x Z_m covers.  Usage: search.py q m mode budget seed
mode 'exh': z0=0, z1 over divisors of m (unit normalisation), z2,z3 over Z_m (exhaustive).
mode 'rnd': budget random label tuples (z0=0, z1 random divisor-normalised, z2,z3 random).
Prints one line per evaluated tuple that is FULL (compA==compB==V) with diameter <= 10, then a SUMMARY json."""
import sys, subprocess, json, random, os
HERE = '/home/user/degree-diameter/research/theorems/haar_families'
q, m, mode, budget, seed = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5])
random.seed(seed)
V = q * (q * q - 1) * m
base = subprocess.run(['python3', f'{HERE}/gen_lps_cover.py', '3', str(q), str(m), 'zero'], capture_output=True, text=True).stdout.split('\n')
base = [L.split()[:4] for L in base if L.strip()]
divs = [d for d in range(1, m + 1) if m % d == 0]
def ev(z):
    lines = '\n'.join(' '.join(b) + f' {z[i]}' for i, b in enumerate(base)) + '\n'
    r = subprocess.run([f'{HERE}/haar_ecc', 'pgl', str(q), str(m), '-D', '10'], input=lines, capture_output=True, text=True)
    import re
    mm = re.search(r'ecc_A=(\d+) ecc_B=(\d+) compA=(\d+) compB=(\d+)', r.stdout)
    if not mm: return None
    eA, eB, cA, cB = map(int, mm.groups())
    full = cA == V and cB == V
    return (max(eA, eB) if full else None), full
if mode == 'exh':
    tuples = ((0, d, z2, z3) for d in divs for z2 in range(m) for z3 in range(m))
else:
    tuples = ((0, random.choice(divs), random.randrange(m), random.randrange(m)) for _ in range(budget))
best = {}; n = 0; nfull = 0; hist = {}
for z in tuples:
    n += 1
    res = ev(z)
    if res is None: continue
    dia, full = res
    if not full: continue
    nfull += 1
    hist[dia] = hist.get(dia, 0) + 1
    for D in (8, 9, 10):
        if dia <= D and (D not in best or V > best[D][0]):
            best[D] = (V, z)
    if dia <= 10 and (dia <= 9 or V > 2000):
        pass
print(json.dumps({'q': q, 'm': m, 'V': V, 'evals': n, 'full': nfull, 'diam_hist': hist,
                  'best': {D: {'V': v[0], 'z': v[1]} for D, v in best.items()}}))
