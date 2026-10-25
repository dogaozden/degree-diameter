#!/usr/bin/env python3
"""hd5_drop.py: hub-slot assignment for a five-level relaxed state (tmL_build.py assign); while some pairs cannot be
served, drop one end of each unserved pair from its set and rerun. Prints the hub counts and n = 10N + KB + KA.
usage: hd5_drop.py HEXBIN MIRROR_SOL STATEDIR SEED OUT.sol"""
import sys, os, subprocess
import numpy as np
D = os.path.dirname(os.path.abspath(__file__))
hexfn, mirfn, sd, seed, out = sys.argv[1:6]
NAME = {(0, 1): 'P01', (1, 1): 'L12', (2, 1): 'P23', (3, 1): 'L34', (3, 2): 'L30', (4, 2): 'P41'}
spec = os.path.join(sd, 'spec.txt')
with open(spec, 'w') as f:
    f.write('T HDHDH\n' + ''.join(f'{j} {k} {nm}.txt\n' for (j, k), nm in NAME.items()))
for it in range(30):
    r = subprocess.run([sys.executable, os.path.join(D, 'tmL_build.py'), 'assign', hexfn, mirfn, spec, seed, out],
                       capture_output=True, text=True)
    if r.returncode == 0: break
    assert r.returncode == 3, r.stdout + r.stderr
    drops = {}
    for line in open(out + '.unserved'):
        j, j2, a, b = map(int, line.split()); k = (j2 - j) % 5
        drops.setdefault(NAME[(j, k)], set()).add(a)
    for nm, s in drops.items():
        fn = os.path.join(sd, nm + '.txt'); ids = np.loadtxt(fn, dtype=np.int64).reshape(-1)
        np.savetxt(fn, ids[~np.isin(ids, list(s))], fmt='%d')
        print(f'  dropped {len(s)} from {nm}', flush=True)
else:
    sys.exit('did not converge')
last = [l for l in r.stdout.split('\n') if l.startswith('free A-slots')][-1]
KB, KA = (int(v) for v in last.split('-> hubs')[1].split())
N = int(np.frombuffer(open(hexfn, 'rb').read(12), np.int32)[1])
print(last)
print(f'SCORE n = {10 * N + KB + KA} (hubs {KB} + {KA}); sets', {nm: len(np.loadtxt(os.path.join(sd, nm + ".txt"))) for nm in NAME.values()})
