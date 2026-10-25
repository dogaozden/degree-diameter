#!/usr/bin/env python3
"""v3_drop.py: run tm3_build.py assign; while some pairs cannot be served, drop one end of each unserved pair from its
transition's set file (the set files are rewritten in place, keeping a .orig copy) and rerun.
usage: v3_drop.py HEXBIN MIRROR_SOL SETSPEC SEED OUT.sol"""
import sys, os, subprocess, shutil
import numpy as np
hexfn, mirfn, spec, seed, out = sys.argv[1:6]
d = os.path.dirname(os.path.abspath(spec))
files = {}
for line in open(spec):
    t = line.split()
    if t and not t[0].startswith('#') and t[0] != 'T': files[(int(t[0]), int(t[1]))] = os.path.join(d, t[2])
T = 'HHDHHDD'
for it in range(20):
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'tm3_build.py'), 'assign',
                        hexfn, mirfn, spec, seed, out], capture_output=True, text=True)
    print(r.stdout, end='', flush=True)
    if r.returncode == 0: break
    assert r.returncode == 3, r.stderr
    drops = {}
    with open(out + '.unserved.all', 'a') as fa: fa.write(open(out + '.unserved').read())
    for line in open(out + '.unserved'):
        j, j2, a, b = map(int, line.split()); k = (j2 - j) % 7
        drops.setdefault((j, k), set()).add(a)          # drop the smaller id of the pair (either end works)
    for key, s in drops.items():
        fn = files[key]
        if not os.path.exists(fn + '.orig'): shutil.copy(fn, fn + '.orig')
        ids = np.loadtxt(fn, dtype=np.int64).reshape(-1)
        keep = ids[~np.isin(ids, list(s))]
        np.savetxt(fn, keep, fmt='%d')
        print(f'  dropped {len(ids) - len(keep)} from {os.path.basename(fn)} -> {len(keep)}', flush=True)
else:
    sys.exit('did not converge')
