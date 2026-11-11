#!/usr/bin/env python3
# sweep5.py BASE D n_list lambda_max_count timeout : EXH liftsym over given primes (own copy of lsym/sweep.py, paths local)
import sys, subprocess, os
here = os.path.dirname(os.path.abspath(__file__))
LS = '/home/user/degree-diameter/research/frontier/bin/liftsym'
base, D = sys.argv[1], int(sys.argv[2]); ns = [int(x) for x in sys.argv[3].split(',')]
maxlam = int(sys.argv[4]); tmo = int(sys.argv[5])
os.makedirs(f'{here}/out', exist_ok=True)
perm = list(map(int, open(f'{here}/{base}.perm').read().split())); b = len(perm)
k = 1; cur = perm[:]
while cur != list(range(b)): cur = [perm[x] for x in cur]; k += 1
for n in ns:
    lams = [l for l in range(2, n) if pow(l, k, n) == 1 and all(pow(l, j, n) != 1 for j in range(1, k))][:maxlam]
    for l in lams:
        tag = f'{base}_D{D}_n{n}_l{l}'
        r = subprocess.run(['timeout', str(tmo), LS, f'{here}/{base}.txt', f'{here}/{base}.perm', str(n), str(l), str(D), '1', '1', f'{here}/out/{tag}'],
                           env=dict(os.environ, EXH='1', THREADS='1'), capture_output=True, text=True)
        line = [x for x in r.stdout.split('\n') if x.startswith('EXHRESULT')]
        res = line[0] if line else 'TIMEOUT/FAIL'
        print(tag, b * n, res, flush=True)
        if 'solutions=' in res and 'solutions=0' not in res: print('FOUND', tag, b * n, flush=True)
