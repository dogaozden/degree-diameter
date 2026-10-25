"""c6 step 2: structure of Stab(R756) inside N(<h>) (from stab_R756.json): element orders, subgroups of order 2..12
up to conjugacy, written as generator matrices (standard coordinates) for orbclq.
The group acts faithfully on the 756 points of R756; elements are indexed and a multiplication table is built."""
import os, sys, json
from collections import Counter
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

HERE = os.path.dirname(os.path.abspath(__file__))
data = json.load(open(os.path.join(HERE, 'stab_R756.json')))
mats = [np.array(M, dtype=np.int64) % Q for M in data['elements']]
R = load_points(R756_PATH)
idx = {tuple(int(v) for v in r): i for i, r in enumerate(R)}
n = len(R)


def perm_of(M):
    img = normalize_rows((R @ M.T) % Q)
    return np.array([idx[tuple(int(v) for v in r)] for r in img], dtype=np.int64)


perms = [perm_of(M) for M in mats]
N = len(perms)
keys = {tuple(p.tolist()): i for i, p in enumerate(perms)}
assert len(keys) == N
ident = [i for i, p in enumerate(perms) if np.all(p == np.arange(n))][0]
# multiplication table: mul[a][b] = index of (apply a then b) = perms[b][perms[a]]
mul = np.zeros((N, N), dtype=np.int64)
for a in range(N):
    for b in range(N):
        mul[a, b] = keys[tuple(perms[b][perms[a]].tolist())]
# closure check
assert all(mul[a, b] in range(N) for a in range(N) for b in range(N))
inv = np.array([int(np.nonzero(mul[a] == ident)[0][0]) for a in range(N)])
print('group order', N, flush=True)


def gen_closure(gens):
    S = {ident}; frontier = [ident]
    while frontier:
        nf = []
        for x in frontier:
            for g in gens:
                y = int(mul[x, g])
                if y not in S:
                    S.add(y); nf.append(y)
        frontier = nf
    return frozenset(S)


ordv = {}
for a in range(N):
    k = 1; x = a
    while x != ident:
        x = int(mul[x, a]); k += 1
    ordv[a] = k
print('element orders:', sorted(Counter(ordv.values()).items()), flush=True)
cyc = list({gen_closure([a]) for a in range(N)})
print('cyclic subgroups:', len(cyc), flush=True)
subs = set(cyc)
frontier = list(cyc)
while frontier:
    nf = []
    for A in frontier:
        for C in cyc:
            if C <= A: continue
            J = gen_closure(list(A | C))
            if J not in subs:
                subs.add(J); nf.append(J)
    frontier = nf
print('all subgroups:', len(subs), flush=True)


def conj(S, g):
    gi = int(inv[g])
    return frozenset(int(mul[mul[gi, s], g]) for s in S)


reps = []; seen = set()
for S in sorted(subs, key=len):
    if S in seen: continue
    cls = {conj(S, g) for g in range(N)}
    seen |= cls
    reps.append((S, len(cls)))
print('conjugacy classes of subgroups:', len(reps), flush=True)
out = []
for S, ncls in reps:
    if 2 <= len(S) <= 12:
        gens = []; cur = frozenset([ident])
        for p in sorted(S, key=lambda q: -ordv[q]):
            if p not in cur:
                gens.append(p); cur = gen_closure(gens)
            if len(cur) == len(S): break
        assert len(cur) == len(S)
        out.append({'order': len(S), 'conj_class_size': ncls, 'gen_orders': [ordv[g] for g in gens],
                    'gens': [mats[g].tolist() for g in gens], 'elements_idx': sorted(S)})
        print(f'subgroup order {len(S):2d}  #conj {ncls:2d}  generator orders {[ordv[g] for g in gens]}', flush=True)
json.dump(out, open(os.path.join(HERE, 'subgroups_2_12.json'), 'w'))
print('saved', len(out), 'subgroup classes of order 2..12', flush=True)
