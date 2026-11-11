#!/usr/bin/env python3
# w01 driver: Gray graph (54 v), rho = order-9 rotation, lambda of ORDER 3 (non-maximal), exhaustive liftsym EXH=1.
import subprocess, os, sys
F = '/home/user/degree-diameter/research/frontier'
W = '/home/user/degree-diameter/research/squads/beyond15/r2/w01'
base = f'{F}/beyond15/lsym/gray.txt'; perm = f'{F}/beyond15/lsym/gray.perm'
def isprime(x): return x > 1 and all(x % p for p in range(2, int(x**.5) + 1))
jobs = []
for D, lo, hi in [(15, 200, 300), (16, 327, 420)]:
    for n in range(lo, hi + 1):
        if isprime(n) and n % 3 == 1:
            lams = [l for l in range(2, n) if pow(l, 3, n) == 1]
            for l in lams: jobs.append((D, n, l))
log = open(f'{W}/run_log.txt', 'a')
for D, n, l in jobs:
    tag = f'gray_D{D}_n{n}_l{l}'
    r = subprocess.run(['timeout', '100', f'{F}/bin/liftsym', base, perm, str(n), str(l), str(D), '1', '1', f'{W}/out/{tag}'],
                       env=dict(os.environ, EXH='1', THREADS='1'), capture_output=True, text=True)
    line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT')]
    res = line[0] if line else 'TIMEOUT/FAIL'
    print(tag, 54 * n, res, file=log, flush=True)
    if 'solutions=' in res and 'solutions=0' not in res:
        print('FOUND', tag, 54 * n, file=log, flush=True)
    else:
        for ext in ('.best', '.edges'):
            try: os.remove(f'{W}/out/{tag}{ext}')
            except FileNotFoundError: pass
print('DONE', file=log, flush=True)
