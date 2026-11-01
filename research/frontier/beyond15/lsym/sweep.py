#!/usr/bin/env python3
"""sweep.py BASE D nlo nhi [maxlam] [timeout]: exhaustive symmetric lifts (liftsym EXH=1) of lsym/BASE.txt with rho = lsym/BASE.perm
for every prime n in [nlo, nhi] with k | n-1 and every lambda of exact order k (up to maxlam of them); prints one line per run,
'FOUND' lines for solutions (edge list lsym/out/<tag>.edges)."""
import sys, subprocess, math, os
base, D, lo, hi = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
maxlam = int(sys.argv[5]) if len(sys.argv) > 5 else 99; tmo = int(sys.argv[6]) if len(sys.argv) > 6 else 100
here = os.path.dirname(os.path.abspath(__file__)); os.makedirs(f'{here}/out', exist_ok=True)
b = int(open(f'{here}/{base}.txt').readline())
perm = list(map(int, open(f'{here}/{base}.perm').read().split()))
k = 1; cur = perm[:]
while cur != list(range(b)): cur = [perm[x] for x in cur]; k += 1
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x**.5) + 1))
for n in range(lo, hi + 1):
    if not isprime(n) or (n - 1) % k: continue
    lams = [l for l in range(2, n) if pow(l, k, n) == 1 and all(pow(l, j, n) != 1 for j in range(1, k))][:maxlam]
    for l in lams:
        tag = f'{base}_D{D}_n{n}_l{l}'
        r = subprocess.run(['timeout', str(tmo), f'{here}/../bin/liftsym', f'{here}/{base}.txt', f'{here}/{base}.perm', str(n), str(l), str(D), '1', '1', f'{here}/out/{tag}'],
                           env=dict(os.environ, EXH='1'), capture_output=True, text=True)
        line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT')]
        res = line[0] if line else 'TIMEOUT/FAIL'
        print(tag, b * n, res, flush=True)
        if 'solutions=' in res and 'solutions=0' not in res: print('FOUND', tag, b * n, flush=True)
        else:
            for ext in ('.best', '.edges'):
                try: os.remove(f'{here}/out/{tag}{ext}')
                except FileNotFoundError: pass
