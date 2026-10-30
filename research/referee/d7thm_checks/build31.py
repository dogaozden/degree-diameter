#!/usr/bin/env python3
"""Referee's rebuild of the graph of Theorem 3.1 of D7_THEOREMS.md from the printed definitions, with own code.
  H(q) from hexlib.py; Hermitian spread S = H-lines in Pi (q odd: X0 + c X4 = 0, -c a non-square; q even:
  X3 = X0 + delta X4, Tr delta = 1); v = <e1, e6>; Pi_z, S_z, nu, G, F, W exactly as in POLISHED.md §6.3 / §6.5;
  R_H = points of S; R_L = L_v + W + S_0(W) (Definition 1.1); non-friendly sets: the q^2+1 points of an elliptic
  quadric section of a 3-space and q^2+1 lines of S, sigma as in D7_HEXAGON.md Prop. 5.2 (random choices);
  alternating layout on Z_{2k+1} (Theorem 2.2), identity on friendly transitions, sigma / sigma^{-1} on H->H / D->D;
  K_B, K_A hubs attached to random free slots; hub graph given as an argument.
Checks (asserts) every statement of Lemma 1.2(c),(d), Theorem 1.4(a)-(c), Lemma 1.6, Theorem 1.7, Corollary 1.8,
Proposition 1.9 on the way, then writes the edge list for bfsd.c.
Usage: build31.py q k hubgraph out.edges [seed] [control]
  hubgraph: 'edge' (one edge), 'c12' (12-cycle), 'H<s>' (incidence graph of H(s)), 'H<s>+H<t>' (Lemma 4.2 sum),
            or a file name 'file:<path>' (first line 'K1 K2', then edges 'i j', i < K1 a B-hub, j < K2 an A-hub)
  control: 'nohubgraph' (drop the hub graph edges: should fail), 'none' (default)"""
import sys, random, itertools, time
import numpy as np
from hexlib import Hexagon, GF, normalize, dist_array

q, k = int(sys.argv[1]), int(sys.argv[2]); hubspec = sys.argv[3]; outf = sys.argv[4]
seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
control = sys.argv[6] if len(sys.argv) > 6 else 'none'
random.seed(seed)
t0 = time.time()
H = Hexagon(q); F = H.F; M, A, S_ = F.mul, F.add, F.sub; n = H.N; X = H.X; even = H.even
adj = H.incidence_adj()
def ev(f):   # evaluate f on all points (vectorised over the coordinates)
    return f(*[X[:, i] for i in range(7)])
lines = H.lines
pt_of_line = [set(L) for L in lines]
def line_in(mask):   # lines all of whose points satisfy mask
    return [li for li, L in enumerate(lines) if all(mask[p] for p in L)]

# --- the hyperplanes Pi_z and their spreads
if not even:
    nonsq = [c for c in range(1, q) if F.neg[c] not in F.squares]     # -c non-square
    c = nonsq[0]
    def Piz(al, be): return ev(lambda X0, X1, X2, X3, X4, X5, X6: A[A[A[X0, M[c, X4]], M[al, X2]], M[be, X5]] == 0)
    def nu_num(X0, X1, X2, X3, X4, X5, X6): return S_[M[X2, X3], M[X4, X5]]
    def nu_den(X0, X1, X2, X3, X4, X5, X6): return A[M[c, M[X2, X2]], M[X5, X5]]
    def Nform(a, b): return A[M[a, a], M[c, M[b, b]]]
    def G(a, b, c0, c1): return S_[M[A[M[c0, a], M[c1, b]], Nform(a, b)], M[b, M[b, b]]]
else:
    c = [d for d in range(1, q) if F.tr(d) == 1][0]      # delta
    def Piz(al, be): return ev(lambda X0, X1, X2, X3, X4, X5, X6: X3 == A[A[A[X0, M[c, X4]], M[al, X2]], M[be, X5]])
    def nu_num(X0, X1, X2, X3, X4, X5, X6): return A[A[M[X2, X3], M[X2, X4]], M[X4, X5]]
    def nu_den(X0, X1, X2, X3, X4, X5, X6): return A[A[M[c, M[X2, X2]], M[X2, X5]], M[X5, X5]]
    def Nform(a, b): return A[A[M[a, a], M[a, b]], M[c, M[b, b]]]
    def G(a, b, c0, c1): return A[M[A[M[c0, a], M[c1, b]], Nform(a, b)], M[b, M[b, b]]]
# c0, c1 with G zero-free on F^2 \ 0
good = [(c0, c1) for c0 in range(q) for c1 in range(q)
        if all(G(a, b, c0, c1) != 0 for a in range(q) for b in range(q) if (a, b) != (0, 0))]
assert good, 'no zero-free G (q = 2?)'
c0, c1 = good[0]
print('q=%d k=%d: %s = %d, (c0, c1) = (%d, %d) (%d admissible pairs)' % (q, k, 'delta' if even else 'c', c, c0, c1, len(good)))
inPi = Piz(0, 0)
Spread = line_in(inPi)
assert len(Spread) == q**3 + 1
e1 = H.index[(0, 1, 0, 0, 0, 0, 0)]; e6 = H.index[(0, 0, 0, 0, 0, 0, 1)]
v = [li for li in H.on[e1] if e6 in pt_of_line[li]][0]
assert v in Spread
PS = sorted({p for li in Spread for p in lines[li]})                      # R_H
assert len(PS) == (q + 1) * (q**3 + 1)
dv = dist_array(adj, n + v)
# Lemma 1.2
assert all(dv[p] == 5 for p in PS if p not in pt_of_line[v])               # (b)
PSset = set(PS)
free = [p for p in range(n) if dv[p] == 5 and p not in PSset]
assert len(free) == q**3 * (q * q - 1)                                     # (c)
Lv = [li for li in range(n) if li != v and dv[n + li] == 2]
assert len(Lv) == q * (q + 1)
# spreads S_z and the whisker set
nu = {}
num, den = ev(nu_num), ev(nu_den)
for p in PS:
    if p not in pt_of_line[v]:
        assert den[p] != 0
        nu[p] = int(M[num[p], F.inv[den[p]]])
W = []; Sz = {}
for al in range(q):
    for be in range(q):
        if (al, be) == (0, 0): continue
        Sz[(al, be)] = line_in(Piz(al, be))
        assert len(Sz[(al, be)]) == q**3 + 1 and v in Sz[(al, be)]
        Fz = int(M[G(al, be, c0, c1), F.inv[Nform(al, be)]])
        for li in Sz[(al, be)]:
            if li == v: continue
            meet = [p for p in lines[li] if inPi[p]]
            assert len(meet) == 1                         # Lemma 6.1(c): one point in Pi
            if nu[meet[0]] == Fz: W.append(li)
W = sorted(W); Wset = set(W)
assert len(Wset) == len(W) == q * q * (q * q - 1)
assert all(dv[n + w] == 6 and w not in Spread for w in W)                  # whiskers opposite v, not in S
cover = {}
for w in W:
    for p in lines[w]:
        if p not in PSset: cover[p] = cover.get(p, 0) + 1
assert sorted(cover) == sorted(free) and set(cover.values()) == {1}        # exact
# Theorem 1.7: nu constant on spread lines, 0 or q+1 whiskers per spread line, |S_0| = q^2
S0 = []
for li in Spread:
    if li == v: continue
    vals = {nu[p] for p in lines[li]}
    assert len(vals) == 1
    nw = sum(1 for p in lines[li] for w in H.on[p] if w in Wset)
    assert nw in (0, q + 1) and (nw == 0) == (vals == {0})
    if nw == 0: S0.append(li)
assert len(S0) == q * q
RL = sorted(set(Lv) | Wset | set(S0)); RLset = set(RL)
assert len(RL) == q**4 + q**2 + q
# Theorem 1.4(a): dual segment set, meeting points in P_S; (c): maximal
for li in RL:
    pts = [p for p in lines[li] if any(l2 in RLset and l2 != li for l2 in H.on[p])]
    assert len(pts) <= 1 and all(p in PSset for p in pts)
for li in range(n):
    if li in RLset: continue
    pts = [p for p in lines[li] if any(l2 in RLset for l2 in H.on[p])]
    assert len(pts) >= 2                                                    # adding li breaks the property
# segment property of P_S
for p in PS:
    ls = [l for l in H.on[p] if any(p2 != p and p2 in PSset for p2 in lines[l])]
    assert len(ls) <= 1
print('  sets: |P_S| = %d segment set; |W| = %d exact; |S_0| = %d (nu = 0); |R_L| = %d dual segment set, maximal' % (
    len(PS), len(W), len(S0), len(RL)))

# --- Proposition 1.9: elliptic quadric section of a 3-space, q^2+1 pairwise opposite points
def span_points(basis):
    pts = set()
    for coef in itertools.product(range(q), repeat=len(basis)):
        if not any(coef): continue
        w = [0] * 7
        for cf, b in zip(coef, basis):
            for i in range(7): w[i] = int(A[w[i], M[cf, b[i]]])
        w = normalize(F, w)
        if w in H.index: pts.add(H.index[w])
    return sorted(pts)
def unit(i): return [1 if j == i else 0 for j in range(7)]
if not even:
    t = [x for x in range(1, q) if x not in F.squares][0]
    basis = [unit(0), unit(4), unit(3), [0, 1, 0, 0, 0, t, 0]]
else:
    basis = [unit(0), unit(4), [0, 1, 0, 1, 0, 0, 0], [0, c, 0, 0, 0, 1, 0]]
R = span_points(basis)
assert len(R) == q * q + 1, len(R)
dR = {x: dist_array(adj, x) for x in R}
assert all(dR[x][y] == 6 for x in R for y in R if x != y)
Rstar = Spread[:q * q + 1]
# sigma: P -> L with sigma(R) = R*, sigma(Gamma_2(x)) = Gamma_2(sigma(x)) (D7_HEXAGON Prop. 5.2, random choices)
sigma = {}
usedL = set()
order = list(range(len(R))); random.shuffle(order)
for i, x in enumerate(R):
    y = Rstar[order[i]]; sigma[x] = y; usedL.add(y)
    g2x = [p for p in range(n) if dR[x][p] == 2]
    g2y = sorted({l2 for p in lines[y] for l2 in H.on[p] if l2 != y})
    assert len(g2x) == len(g2y) == q * (q + 1)
    random.shuffle(g2y)
    for p, l2 in zip(g2x, g2y):
        assert p not in sigma and l2 not in usedL
        sigma[p] = l2; usedL.add(l2)
restP = [p for p in range(n) if p not in sigma]; restL = [l for l in range(n) if l not in usedL]
random.shuffle(restL)
for p, l in zip(restP, restL): sigma[p] = l
assert sorted(sigma.values()) == list(range(n))
sigma_inv = {l: p for p, l in sigma.items()}
Rst = [sigma[x] for x in R]
# (H1)-(H3)
for x in R:
    g2x = {p for p in range(n) if dR[x][p] == 2}
    assert not (g2x & set(R))
    g2s = {l2 for p in lines[sigma[x]] for l2 in H.on[p] if l2 != sigma[x]}
    assert {sigma[p] for p in g2x} == g2s and not (g2s & set(Rst))
print('  non-friendly: %d pairwise opposite points of an elliptic quadric section, sigma a local duality at each' % len(R))

# --- layout
L = 2 * k + 1
types = ['H' if j % 2 == 0 else 'D' for j in range(L)]
VN = 2 * n                     # vertices per level: points 0..n-1, lines n..2n-1
def vid(j, e): return j * VN + e
edges = []
for j in range(L):
    for li, Lp in enumerate(lines):
        for p in Lp: edges.append((vid(j, p), vid(j, n + li)))
Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
for j in range(L):
    for i in range(1, k + 1):
        j2 = (j + i) % L
        if types[j] != types[j2]:
            if types[j] == 'H':   # points -> points, identity, freed P_S
                Aset = range(n); Mt = lambda a: a; Rt = PSset; enc = lambda a: a; encB = lambda b: b
            else:                 # lines -> lines, identity, freed R_L
                Aset = range(n); Mt = lambda a: a; Rt = RLset; enc = lambda a: n + a; encB = lambda b: n + b
        else:
            if types[j] == 'H':   # points -> lines by sigma, freed R
                Aset = range(n); Mt = lambda a: sigma[a]; Rt = set(R); enc = lambda a: a; encB = lambda b: n + b
            else:                 # lines -> points by sigma^-1, freed sigma(R)
                Aset = range(n); Mt = lambda a: sigma_inv[a]; Rt = set(Rst); enc = lambda a: n + a; encB = lambda b: b
        for a in Aset:
            if a in Rt:
                Aslots[j].append(vid(j, enc(a))); Bslots[j2].append(vid(j2, encB(Mt(a))))
            else:
                edges.append((vid(j, enc(a)), vid(j2, encB(Mt(a)))))
alpha = [len(s) for s in Aslots]; beta = [len(s) for s in Bslots]
P_, Lam_, m_ = (q + 1) * (q**3 + 1), q**4 + q**2 + q, q * q + 1
a_ = k // 2
expKB = a_ * (Lam_ + m_) if k % 2 == 0 else a_ * P_ + (a_ + 1) * m_
expKA = a_ * (Lam_ + m_) if k % 2 == 0 else a_ * Lam_ + (a_ + 1) * m_
assert min(alpha) == expKB and min(beta) == expKA, (alpha, beta)
print('  layout %s: alpha %s beta %s; min = (%d, %d) = Theorem 2.2' % (''.join(types), alpha, beta, min(alpha), min(beta)))

# --- hub graph
def hex_incidence(s):
    Hs = Hexagon(s)
    return Hs.N, Hs.N, [(p, li) for li, Lp in enumerate(Hs.lines) for p in Lp]
def blow_sum(specs):     # Lemma 4.2: parts listed in order, injections A_j -> B_i and B_j -> A_i for i < j
    parts = [hex_incidence(int(s)) for s in specs]
    offA = [0]; offB = [0]
    for (a, b, e) in parts: offA.append(offA[-1] + a); offB.append(offB[-1] + b)
    E = []
    for i, (a, b, e) in enumerate(parts):
        E += [(offA[i] + x, offB[i] + y) for (x, y) in e]
    for i in range(len(parts)):
        for j in range(i + 1, len(parts)):
            ai, bi, _ = parts[i]; aj, bj, _ = parts[j]
            assert aj <= bi and bj <= ai
            imgB = random.sample(range(bi), aj)    # A_j -> B_i
            imgA = random.sample(range(ai), bj)    # B_j -> A_i
            E += [(offA[j] + x, offB[i] + imgB[x]) for x in range(aj)]
            E += [(offA[i] + imgA[y], offB[j] + y) for y in range(bj)]
    return offA[-1], offB[-1], E
if hubspec == 'edge': K1, K2, Y = 1, 1, [(0, 0)]
elif hubspec == 'c12': K1, K2, Y = 6, 6, [(i, i) for i in range(6)] + [(i, (i + 1) % 6) for i in range(6)]
elif hubspec.startswith('file:'):
    fl = open(hubspec[5:]).read().split('\n'); K1, K2 = map(int, fl[0].split()); Y = [tuple(map(int, x.split())) for x in fl[1:] if x.strip()]
else:
    K1, K2, Y = blow_sum([s.strip('H') for s in hubspec.split('+')])
assert K1 <= min(alpha) and K2 <= min(beta)
degY = {}
for (a, b) in Y: degY[('B', a)] = degY.get(('B', a), 0) + 1; degY[('A', b)] = degY.get(('A', b), 0) + 1
assert max(degY.values()) <= q - k, max(degY.values())
base = L * VN
hubB = [base + i for i in range(K1)]; hubA = [base + K1 + i for i in range(K2)]
for j in range(L):
    sa = random.sample(Aslots[j], K1); sb = random.sample(Bslots[j], K2)
    for i in range(K1): edges.append((hubB[i], sa[i]))
    for i in range(K2): edges.append((hubA[i], sb[i]))
if control != 'nohubgraph':
    for (a, b) in Y: edges.append((hubB[a], hubA[b]))
ntot = base + K1 + K2
with open(outf, 'w') as f:
    f.write('%d %d\n' % (ntot, len(edges)))
    for (u, w) in edges: f.write('%d %d\n' % (u, w))
print('  hub graph %s: %d + %d hubs, max degree %d <= q-k = %d; n = %d = 2(2k+1)N + K1 + K2 = %d; wrote %s (%.1fs)' % (
    hubspec, K1, K2, max(degY.values()), q - k, ntot, 2 * L * n + K1 + K2, outf, time.time() - t0))
