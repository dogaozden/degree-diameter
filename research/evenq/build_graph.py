"""Delorme's levels on H(q) + a whisker file -> plain edge list (first line n, then 'u v'), then bigcheck.

python3 build_graph.py WHISKERS.json ARITY OUT.txt [--nocheck]
"""
import json
import subprocess
import sys

import numpy as np

from hexq import load

BIGCHECK = '/Users/dogaozden/AI_Projects/research-lab/verify/bigcheck/bigcheck'
d = json.load(open(sys.argv[1]))
m_, out = int(sys.argv[2]), sys.argv[3]
q, S, v, W = d['q'], d['S'], d['v'], d['whiskers']
H = load(q)
N, lines, through = H.N, H.lines, H.through
lev = np.full(2 * N, -1)
for s in S:
    if s != v:
        lev[N + s] = 1
        lev[lines[s]] = 0
lev[N + v] = 2
for p in lines[v]:
    lev[p] = 1
    for k in through[p]:
        if k != v:
            lev[N + k] = 0
assert len(set(W)) == len(W)
for k in W:
    assert lev[N + k] == -1
    lev[N + k] = 0
nver = np.where(lev < 0, 1, m_ ** (lev + 1))
first = np.concatenate([[0], np.cumsum(nver)[:-1]])
n = int(nver.sum())
ne = 0
with open(out, 'w') as fh:
    fh.write(f'{n}\n')
    for k in range(N):
        for p in lines[k]:
            a, b = int(p), N + k
            la, lb = int(lev[a]), int(lev[b])
            if la > lb:
                a, b, la, lb = b, a, lb, la
            na = 1 if la < 0 else m_ ** (la + 1)
            ext = 1 if lb < 0 else m_ ** (lb + 1 - (la + 1 if la >= 0 else 0))
            buf = []
            for ia in range(na):
                for e2 in range(ext):
                    ib = ia * ext + e2 if la >= 0 else e2
                    buf.append(f'{first[a] + ia} {first[b] + ib}\n')
            fh.write(''.join(buf))
            ne += len(buf)
formula = 2 * (q + 1) * (q**4 + q**2 + 1) + (m_ - 1) * (q**4 + 2*q**3 + q**2 + 2*q + 2 + len(W) + m_ * (q**3 + q + 2) + m_**2)
print(f'q={q} arity={m_} whiskers={len(W)} n={n} (formula {formula}) edges={ne} -> {out}', flush=True)
if '--nocheck' not in sys.argv:
    r = subprocess.run(['nice', '-n', '15', BIGCHECK, '-t', '4', out, str(q + m_), '6'], capture_output=True, text=True)
    print(r.stdout.strip())
