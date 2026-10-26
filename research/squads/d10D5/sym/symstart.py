#!/usr/bin/env python3
"""symstart.py SEED OUTPREFIX: a g-invariant start for the 8-flag orbit with all 8 flags converted (FLAGDEL, H = 3):
sigma g-equivariant with sigma(p_i) = l_i, chosen by a random perfect matching of the 49 x 49 orbit quotient of the
exact-coverage rules (r1/c5 Matcher); nu g-invariant random; circulant hub graph: own pairs (3i+t ~ 3i+t) and
line-side hub (i,t) ~ point-side hub (i+d, t) for d in D_t (D_0 = 1,2,3; D_1 = 4,5,6; D_2 = 7,2,5).
Writes OUTPREFIX.sol (dmhub format) and OUTPREFIX.lift2.sol."""
import sys, os, random
HERE = os.path.dirname(os.path.abspath(__file__)); C5 = os.path.join(HERE, '..', 'r1', 'c5'); sys.path.insert(0, C5)
from sym import load_all, Matcher
seed, outp = int(sys.argv[1]), sys.argv[2]; rng = random.Random(seed)
q, N, lines, lof, coords = load_all(os.path.join(HERE, '..', 'r4', 'gq', 'gq_q7.bin'))
gp, gl = [list(map(int, l.split())) for l in open(os.path.join(HERE, 'g.txt'))]
F = [266, 41, 225, 65, 263, 283, 398, 253]; Lf = [64, 289, 350, 202, 330, 130, 292, 247]
for i in range(8): assert gp[F[i]] == F[(i + 1) % 8] and gl[Lf[i]] == Lf[(i + 1) % 8]
Mt = Matcher(q, N, lines, lof); sz, _ = Mt.size(list(zip(F, Lf)))
# allowed lines per point (recompute adjacency as in Matcher.size)
Pm, Lm, onl, thr, ALL = Mt.Pm, Mt.Lm, Mt.onl, Mt.thr, Mt.ALL
Fm = sum(1 << p for p in F); Flm = sum(1 << l for l in Lf)
lineok = [ALL & ~Flm] * N; ptok = [ALL & ~Fm] * N
for p, l in zip(F, Lf):
    A = Pm[p] & ~onl[l]; G = Lm[l] & ~thr[p]; Ll = Lm[l] & ~(1 << l); Pp = Pm[p] & ~(1 << p)
    for i in range(N):
        if A >> i & 1: lineok[i] &= Ll
        if G >> i & 1: ptok[i] &= Pp
allowed = [[M for M in range(N) if lineok[x] >> M & 1 and ptok[M] >> x & 1] for x in range(N)]
def orbit(perm, x):
    o = [x]
    while perm[o[-1]] != x: o.append(perm[o[-1]])
    return o
porb = {}; preps = []
for x in range(N):
    if x not in porb:
        o = orbit(gp, x); preps.append(x)
        for k, y in enumerate(o): porb[y] = (x, k)
lorb = {}; lreps = []
for M in range(N):
    if M not in lorb:
        o = orbit(gl, M); lreps.append(M)
        for k, y in enumerate(o): lorb[y] = (M, k)
assert all(len(orbit(gp, r)) == 8 for r in preps) and len(preps) == 50
fr = porb[F[0]][0]; frl = lorb[Lf[0]][0]
prs = [r for r in preps if r != fr]; lrs = [r for r in lreps if r != frl]
cand = {r: {} for r in prs}
for r in prs:
    for M in allowed[r]:
        cand[r].setdefault(lorb[M][0], []).append(M)
# random perfect matching point orbits -> line orbits (augmenting paths, randomised order)
match = {}; owner = {}
def aug(r, seen):
    keys = list(cand[r]); rng.shuffle(keys)
    for s in keys:
        if s in seen: continue
        seen.add(s)
        if s not in owner or aug(owner[s], seen):
            owner[s] = r; match[r] = s; return True
    return False
order = prs[:]; rng.shuffle(order)
for r in order: aug(r, set())
print('quotient matching size', len(match), 'of', len(prs), flush=True)
assert len(match) == len(prs)
sig = [-1] * N
for i in range(8): sig[F[i]] = Lf[i]
for r in prs:
    M = rng.choice(cand[r][match[r]]); x, L = r, M
    for k in range(8): sig[x] = L; x = gp[x]; L = gl[L]
assert sorted(sig) == list(range(N))
for x in range(N): assert sig[gp[x]] == gl[sig[x]]
# invariant nu: flag index l*8 + k (k = position of p in lines[l])
fidx = {(p, l): l * 8 + k for l in range(N) for k, p in enumerate(lines[l])}
nu = [-1] * (N * 8)
for l in range(N):
    for k, p in enumerate(lines[l]):
        f = l * 8 + k
        if nu[f] >= 0: continue
        v = rng.randint(0, 1); pp, ll = p, l
        for _ in range(8): nu[fidx[pp, ll]] = v; pp, ll = gp[pp], gl[ll]
hub = []
D = [[1, 2, 3], [4, 5, 6], [7, 2, 5]]
for i in range(8):
    for t in range(3):
        hub.append((3 * i + t, 3 * i + t))
        for d in D[t]: hub.append((3 * i + t, 3 * ((i + d) % 8) + t))
with open(outp + '.sol', 'w') as f:
    f.write('dmhub q 7 H 3 nfree 8 cost -1\nfree ' + ' '.join(map(str, F)) + '\nsigma ' + ' '.join(map(str, sig)) + '\n')
    f.write('mv0 ' + ' '.join(['1'] * N) + '\nmv1 ' + ' '.join(['4'] * N) + '\nnu ' + ' '.join(str(3 * v) for v in nu) + '\n')
    f.write('hubgraph ' + ' '.join('%d %d' % e for e in hub) + '\n')
with open(outp + '.lift2.sol', 'w') as f:
    f.write('7 2 6 7 -1\ncyc 6\n' + ' '.join(map(str, sig)) + '\n' + ' '.join(map(str, sig)) + '\n')
    f.write(' '.join(['1'] * N) + '\n' + ' '.join(['4'] * N) + '\n' + ' '.join(str(3 * v) for v in nu) + '\n')
print('wrote', outp, 'hub edges', len(hub))
