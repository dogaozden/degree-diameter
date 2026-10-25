#!/usr/bin/env python3
"""add1.py GQBIN "p:l ..." SEED: test every flag f=(p,l) disjoint from the given feasible flag set (points and lines
distinct) for exact-coverage perfect matching of set+f (sym.Matcher). Prints feasible extensions and writes add1_SEED.txt.
usage: python3 -I add1.py gq/gq_q7.bin "266:64 41:289 225:350 65:202 263:330 283:130 398:292 253:247" 1"""
import sys, time
sys.path.insert(0, '.')
from sym import *
fn = sys.argv[1]; F0 = [tuple(map(int, t.split(':'))) for t in sys.argv[2].split()]; seed = sys.argv[3]
q, N, lines, lof, coords = load_all(fn)
Mt = Matcher(q, N, lines, lof)
P0 = {p for p, _ in F0}; L0 = {l for _, l in F0}
sz0, _ = Mt.size(F0)
print('base set k', len(F0), 'matching', sz0, 'of', N, flush=True)
feas = []; t0 = time.time(); tests = 0
for p in range(N):
    if p in P0: continue
    for l in lof[p]:
        if l in L0: continue
        sz, _ = Mt.size(F0 + [(p, l)]); tests += 1
        if sz == N:
            feas.append((p, l)); print('FEASIBLE', p, l, 'time %.1f' % (time.time() - t0), flush=True)
print('DONE tests', tests, 'feasible extensions', len(feas), 'time %.1f' % (time.time() - t0), flush=True)
with open(f'add1_{seed}.txt', 'w') as f:
    for p, l in feas: f.write(' '.join(f'{a}:{b}' for a, b in F0 + [(p, l)]) + '\n')
