"""Do the whiskers come from other Hermitian spreads? For every hyperplane through v holding q^3+1 lines of H(q),
count its lines in S, in E (empty S-lines) and in W.  python3 whisk_spread2.py q"""
import itertools
import sys
from collections import Counter

import numpy as np

q = int(sys.argv[1])
sys.argv = ['hexbig_gf.py', str(q), '60', 'nobuild', '--load']
src = open('hexbig_gf.py').read()
exec(compile(src.split('if build and okfree and okX:')[0], 'hexbig_gf.py', 'exec'))
Wset = set(W)
full = {int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in W}
Eset = set(S.tolist()) - full - {v}
vv = P[lines[v][:2]]
res = Counter()
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(x for x in a if x) != 1:
        continue
    av = np.array(a)
    if any(fsum([MUL[w[i], av[i]] for i in range(7)]) for w in vv):
        continue
    inH = fsum([MUL[P[:, i], av[i]] for i in range(7)]) == 0
    Sc = np.nonzero(inH[lines].all(axis=1))[0]
    if len(Sc) != q ** 3 + 1:
        continue
    Sc = set(Sc.tolist())
    res[(len(Sc & set(S.tolist())), len(Sc & Eset), len(Sc & Wset))] += 1
print('hyperplanes through v with q^3+1 lines: (|S\'&S|, |S\'&E|, |S\'&W|) -> count')
for k, cnt in sorted(res.items()):
    print('  ', k, cnt)

# the spreads meeting S only in v: are their whisker sets disjoint, and how do the hyperplanes sit?
special = []
for a in itertools.product(range(q), repeat=7):
    if not any(a) or next(x for x in a if x) != 1:
        continue
    av = np.array(a)
    if any(fsum([MUL[w[i], av[i]] for i in range(7)]) for w in vv):
        continue
    inH = fsum([MUL[P[:, i], av[i]] for i in range(7)]) == 0
    Sc = np.nonzero(inH[lines].all(axis=1))[0]
    if len(Sc) != q ** 3 + 1:
        continue
    Sc = set(Sc.tolist())
    if len(Sc & set(S.tolist())) == 1:
        special.append((a, Sc & Wset))
cover = Counter(k for _, ws in special for k in ws)
print('special spreads', len(special), '; whiskers covered', len(cover), 'of', len(W), '; multiplicities', Counter(cover.values()))
print('hyperplanes:', [a for a, _ in special][:30])

# which S-lines do the whiskers of one special spread meet? group them by blocks through v
offS = Sline_of < 0
bv_pts = np.nonzero(offS & (dist[:N] == 3))[0]
blocks_v = {}
for p in bv_pts:
    B = frozenset(int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in through[p])
    blocks_v.setdefault(B, p)
TV = sorted(sorted(B) for B in blocks_v)
line_block = {s: i for i, B in enumerate(TV) for s in B if s != v}
Eblocks = sorted({line_block[s] for s in Eset})
print('E blocks', Eblocks)
for a, ws in special[:8]:
    hit = [int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in ws]
    bl = Counter(line_block[s] for s in hit)
    print('  spread', a, 'whisker S-lines on blocks', sorted(bl.items()))

groups = {}
for a, ws in special:
    hit = [int(Sline_of[[y for y in lines[k] if Sline_of[y] >= 0][0]]) for k in ws]
    key = tuple(sorted({line_block[s] for s in hit}))
    groups.setdefault(key, []).append((a[2], a[5]))  # (alpha, beta) = coefficients of x2, x5
for key, ab in groups.items():
    print('class', key[:3], '...: (alpha, beta) =', sorted(ab))


def nu(x):
    x = [int(t) for t in x]
    I = int(ADD[MUL[x[2], x[3]], NEG[MUL[x[4], x[5]]]])
    D = int(ADD[MUL[c, MUL[x[2], x[2]]], MUL[x[5], x[5]]])
    return int(MUL[I, INV[D]]) if D else None


const = all(len({nu(P[p]) for p in lines[s]}) == 1 for s in S.tolist() if s != v)
print('nu constant on every S-line other than v:', const)
nuE = {nu(P[lines[s][0]]) for s in Eset}
print('nu on E lines:', nuE)
for key, ab in groups.items():
    s_any = [s for s in S.tolist() if s != v and line_block.get(s) == key[0]][0]
    print('class nu =', nu(P[lines[s_any][0]]), ' spreads (alpha, beta):', sorted(ab))

stat = Counter()
for a, ws in special[:6]:
    av = np.array(a)
    inH = fsum([MUL[P[:, i], av[i]] for i in range(7)]) == 0
    Sc = np.nonzero(inH[lines].all(axis=1))[0]
    for k in Sc:
        k = int(k)
        if k == v:
            continue
        vals = {nu(P[p]) for p in lines[k]}
        stat[(k in Wset, len(vals) == 1)] += 1
print('(whisker?, nu constant on the line?) ->', dict(stat))
# all lines of H(q) with nu constant (and defined) on all points, not in S: are they exactly W?
cnt = Counter()
for k in range(N):
    if k in set(S.tolist()):
        continue
    vals = {nu(P[p]) for p in lines[k]}
    if len(vals) == 1 and None not in vals:
        cnt[(k in Wset, dist[N + k])] += 1
print('non-S lines with nu constant: (in W?, dist from v) ->', dict(cnt))

Fz = {}
for key, ab in groups.items():
    s_any = [s for s in S.tolist() if s != v and line_block.get(s) == key[0]][0]
    for (al, be) in ab:
        Fz[(al, be)] = nu(P[lines[s_any][0]])
print('c =', c, ' F(1,m) =', [Fz[(1, m)] for m in range(q)], ' F(0,1) =', Fz[(0, 1)])
sols = []
for p_, r_, A_, B_, C_ in itertools.product(range(q), repeat=5):
    if not (p_ or r_):
        continue
    if all(int(MUL[f, ADD[MUL[p_, al], MUL[r_, be]]]) == int(fsum([MUL[A_, MUL[al, al]], MUL[B_, MUL[al, be]], MUL[C_, MUL[be, be]]])) for (al, be), f in Fz.items()):
        sols.append((p_, r_, A_, B_, C_))
print('F (p a + r b) = A a^2 + B a b + C b^2 solutions:', sols[:6], len(sols))
