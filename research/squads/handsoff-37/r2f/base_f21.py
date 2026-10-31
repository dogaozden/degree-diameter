"""Quotient of C168.1 by Z7 = <g> with an order-3 s normalising it (s g s^-1 = g^r, r = 2 or 4).
Writes a base file: k, r, sigma (order-3 permutation of base vertices, A = 0..k-1, B = k..2k-1), and the base edges (a, b, t)
with b in 0..k-1 meaning B-vertex k+b and voltage t: lift vertex (u, h) = u*7+h, edges (a,h)-(k+b, h+t).
Representatives are chosen s-equivariantly, so the lifted s is (u,h) -> (sigma u, r h) (gauge c = 0)."""
import sys, pickle
from collections import Counter
lines = open('aut168.txt').read().split('\n')
n = int(lines[0])
auts = [list(map(int, l.split())) for l in lines[1:] if l.strip()]
ident = list(range(n))
def mul(p, q): return [p[q[x]] for x in range(n)]
def inv(p):
    q = [0]*n
    for i, x in enumerate(p): q[x] = i
    return q
def pw(p, e):
    q = ident
    for _ in range(e): q = mul(p, q)
    return q
ex = pickle.load(open('f21_examples.pkl', 'rb'))
g = ex['g']
s = ex['examples'][(3, 4)] if len(sys.argv) < 2 else auts[int(sys.argv[1])]
# find r
G = [pw(g, e) for e in range(7)]
c = mul(mul(s, g), inv(s))
r = [e for e in range(7) if G[e] == c][0]
print('r =', r, 'fixed points of s:', [x for x in range(n) if s[x] == x])
# Z7 orbits: first arbitrary labels, then s-equivariant representatives
orb_of = [None]*n; members = []
for x in range(n):
    if orb_of[x] is None:
        orb = [G[h][x] for h in range(7)]
        assert len(set(orb)) == 7
        for y in orb: orb_of[y] = len(members)
        members.append(orb)
nO = len(members)
rep = [None]*nO
for uid in range(nO):
    if rep[uid] is not None: continue
    orb = members[uid]
    if set(s[y] for y in orb) == set(orb):      # s-invariant orbit: rep = its s-fixed vertex
        v = [y for y in orb if s[y] == y]; assert len(v) == 1; v = v[0]
        rep[uid] = v
    else:
        v = orb[0]; rep[uid] = v
        w = s[v]; rep[orb_of[w]] = w
        w2 = s[w]; rep[orb_of[w2]] = w2
        assert s[w2] == v
reps = [None]*nO
for uid in range(nO):
    pass
# hval: exponent with y = g^h rep[orb]
hval = [None]*n
for uid in range(nO):
    for h in range(7):
        y = G[h][rep[uid]]
        assert orb_of[y] == uid
        hval[y] = h
reps = rep
nb = nO
sigma = [None]*nb
for uid, v in enumerate(reps):
    sv = s[v]
    sigma[uid] = orb_of[sv]
    # s(v) must be exactly g^0 * rep_sigma (h = 0)
    assert hval[sv] == 0, ("gauge not zero", uid, hval[sv])
# sides: A side if vertex in A; determine colouring by BFS
from collections import deque
N = [[] for _ in range(n)]
edges = []
toks = open('c168.edges').read().split()
for i in range(1, len(toks), 2):
    a, b = int(toks[i]), int(toks[i+1]); N[a].append(b); N[b].append(a)
col = [-1]*n; col[0] = 0; dq = deque([0])
while dq:
    x = dq.popleft()
    for y in N[x]:
        if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
Aorbs = sorted({orb_of[x] for x in range(n) if col[x] == 0})
Borbs = sorted({orb_of[x] for x in range(n) if col[x] == 1})
assert len(Aorbs) == len(Borbs) == nb // 2, (len(Aorbs), len(Borbs))
idxA = {u: i for i, u in enumerate(Aorbs)}; idxB = {u: i for i, u in enumerate(Borbs)}
k = nb // 2
# base edges with voltages: rep v of orbit u, neighbours y = g^t v_w
base = []
for uid, v in enumerate(reps):
    if col[v] != 0: continue
    for y in N[v]:
        base.append((idxA[uid], idxB[orb_of[y]], hval[y]))
base = sorted(base)
assert len(base) == 3 * k, len(base)
# sigma in A/B indices
sig = [0]*(2*k)
for uid in range(nb):
    if col[reps[uid]] == 0: sig[idxA[uid]] = idxA[sigma[uid]]
    else: sig[k + idxB[uid]] = k + idxB[sigma[uid]]
fixA = sum(1 for i in range(k) if sig[i] == i); fixB = sum(1 for i in range(k, 2*k) if sig[i] == i)
print('k =', k, 'fixed base vertices A/B:', fixA, fixB, 'sigma cycles:', Counter(len(c) for c in []) or '')
# check invariance of base under (sigma, r)
Eset = set(base)
for (a, b, t) in base:
    # base edge (a, k+b): in the 'a' index scheme; B index b
    sa, sb = sig[a], sig[k+b] - k
    assert (sa, sb, (r*t) % 7) in Eset, ("not invariant", (a, b, t))
print('base invariant under (sigma, r=%d): OK' % r)
out = open(sys.argv[2] if len(sys.argv) > 2 else 'base_f21_k12.txt', 'w')
out.write('k %d\nr %d\nsigma %s\n' % (k, r, ' '.join(map(str, sig))))
for (a, b, t) in base: out.write('%d %d %d\n' % (a, b, t))
out.close()
# lift check: vertices (u,h) -> u*7+h with u = A index for 0..k-1, B index k+b
lift = []
for (a, b, t) in base:
    for h in range(7):
        lift.append((a*7 + h, (k+b)*7 + (h+t) % 7))
with open('lift_check_k%d.edges' % k, 'w') as f:
    f.write('%d\n' % (2*k*7))
    for x, y in lift: f.write('%d %d\n' % (x, y))
print('lift written: n =', 2*k*7, 'edges', len(lift))
