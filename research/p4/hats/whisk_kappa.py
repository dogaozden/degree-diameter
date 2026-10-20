"""Test the orbit invariants kappa = (x2 : x5) and mu = (x2 x3 - x4 x5) / (x5 L) (x2 if x5 = 0), L = x0 + c x4,
on free points, and how the whiskers of the exact solution meet the kappa-classes.  python3 whisk_kappa.py q"""
import sys
from collections import Counter, defaultdict

import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))


def kappa_mu(x):
    x = [int(t) for t in x]
    L = int(ADD[x[0], MUL[c, x[4]]])
    I = int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    if x[5]:
        kap = int(MUL[x[2], INV[x[5]]])
        mu = int(MUL[I, INV[MUL[x[5], L]]])
    else:
        kap = 'inf'
        mu = int(MUL[I, INV[MUL[x[2], L]]])
    return kap, mu


GENS = [perms(kelem(0, 0, lam)) for lam in basis] + [perms(kelem(lam, 0, 0)) for lam in basis] + [(tp, tl)]
orb = {}
for p0 in free_pts:
    p0 = int(p0)
    if p0 in orb:
        continue
    o, fr = {p0}, [p0]
    while fr:
        nf = []
        for p in fr:
            for gp, gl in GENS:
                t = int(gp[p])
                if t not in o:
                    o.add(t)
                    nf.append(t)
        fr = nf
    for p in o:
        orb[p] = p0
inv_of = defaultdict(set)
for p, r in orb.items():
    inv_of[r].add(kappa_mu(P[p]))
print('orbits', len(set(orb.values())), '; invariant constant on each orbit:', all(len(s) == 1 for s in inv_of.values()),
      '; distinct values:', len({next(iter(s)) for s in inv_of.values()}))
pat = Counter()
for k in W:
    ks = [kappa_mu(P[p]) for p in lines[k] if int(p) in orb]
    pat[(len({a for a, b in ks}), len({b for a, b in ks}))] += 1
print('whiskers by (#kappa values, #mu values) on their free points:', dict(pat))
Wset = set(W)
full_set = sorted({int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in W})
base = full_set[0]
print('base S-line', base)
for X in lines[base]:
    X = int(X)
    xk = (int(P[X][2]), int(P[X][5]))
    kx = 'inf' if xk[1] == 0 else int(MUL[xk[0], INV[xk[1]]])
    print(' X kappa', kx, ' X =', P[X].tolist())
    for k in through[X]:
        k = int(k)
        if dist[N + k] != 6 or k in Sset:
            continue
        vals = sorted((kappa_mu(P[p]) for p in lines[k] if int(p) in orb), key=str)
        print('   ', '*' if k in Wset else ' ', vals)

# is mu_k an affine (or Moebius) function of mu_k0 across the q-1 candidates at X?
def fit_affine(pairs):
    (x1, y1), (x2, y2) = pairs[0], pairs[1]
    if x1 == x2:
        return None
    a = int(MUL[ADD[y2, NEG[y1]], INV[ADD[x2, NEG[x1]]]])
    b = int(ADD[y1, NEG[MUL[a, x1]]])
    ok = all(int(ADD[MUL[a, x], b]) == y for x, y in pairs)
    return (a, b) if ok else None


stats = Counter()
for s0 in full_set[:3]:
    for X in lines[s0]:
        X = int(X)
        cands = [int(k) for k in through[X] if dist[N + int(k)] == 6 and int(k) not in Sset]
        tab = [dict(kappa_mu(P[p]) for p in lines[k] if int(p) in orb) for k in cands]
        classes = sorted(tab[0].keys(), key=str)
        k0 = classes[0]
        for k in classes[1:]:
            pairs = [(t[k0], t[k]) for t in tab]
            stats['affine' if fit_affine(pairs) else 'not affine'] += 1
print('mu_k vs mu_k0 across candidates:', dict(stats))


def frank(rows):
    M = [list(map(int, r)) for r in rows]
    rank, col = 0, 0
    M = [r[:] for r in M]
    for col in range(7):
        piv = next((i for i in range(rank, len(M)) if M[i][col]), None)
        if piv is None:
            continue
        M[rank], M[piv] = M[piv], M[rank]
        iv = int(INV[M[rank][col]])
        M[rank] = [int(MUL[iv, x]) for x in M[rank]]
        for i in range(len(M)):
            if i != rank and M[i][col]:
                f = M[i][col]
                M[i] = [int(ADD[a, NEG[MUL[f, b]]]) for a, b in zip(M[i], M[rank])]
        rank += 1
    return rank


for s0 in full_set[:4]:
    ws = [int(k) for X in lines[s0] for k in through[int(X)] if int(k) in Wset]
    pts_ = [P[int(p)] for k in ws for p in lines[k]]
    print('base', s0, 'whiskers', len(ws), 'span rank of whisker points:', frank(pts_),
          ' with v:', frank(pts_ + [P[int(p)] for p in lines[v]]))
