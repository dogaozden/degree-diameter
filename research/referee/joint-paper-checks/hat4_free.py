"""Coordinate-free version of the fourth hat (Section 3, paragraph after Theorem 3.2): any anti-flag (A, ell),
any four points of ell; checked at q=3 (all of ell are hats) and q=4,5 with P among the hats."""
import itertools
from gf import GF
from hat4_ref import norm, diameter, bip
def build_free(q, hats):  # hats: dict role->point of ell, roles 'a','t0','t1','tc'; sigma: t0->tc->t1->t0
    F = GF(q); E = list(F.elts()); M, A_ = F.mul, F.add
    pts = sorted(set(norm(F, v) for v in itertools.product(E, repeat=3) if any(v))); lines = pts
    inc = lambda p, L: A_[A_[M[L[0]][p[0]]][M[L[1]][p[1]]]][M[L[2]][p[2]]] == 0
    A = (1, 0, 0); ell = (1, 0, 0)
    join = lambda p, r: next(L for L in lines if inc(p, L) and inc(r, L))
    lam = {k: join(A, x) for k, x in hats.items()}
    sig = {'t0': 'tc', 'tc': 't1', 't1': 't0'}; T = ['t0', 't1', 'tc']
    adj = {}
    def e(u, v): adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    for p in pts:
        for L in lines:
            if inc(p, L) and not any(p == hats[k] and L == lam[k] for k in hats): e(('p', p), ('L', L))
    for t in T: e(('p', hats[t]), ('L', lam[sig[t]]))
    for k, x in hats.items():
        for L in lines:
            if inc(x, L) and L != ell: e(('H', k), ('L', L))
        for p in pts:
            if inc(p, lam[k]) and p != A: e(('K', k), ('p', p))
    Tpts = {hats[t] for t in T}; Tlin = {lam[t] for t in T}
    for p in pts:
        if inc(p, ell) and p not in Tpts: e(('M',), ('p', p))
    for L in lines:
        if inc(A, L) and L not in Tlin: e(('Q',), ('L', L))
    for k in hats: e(('M',), ('H', k)); e(('Q',), ('K', k))
    e(('p', A), ('K', 'a')); e(('H', 'a'), ('L', ell))
    for t in T: e(('H', t), ('K', sig[t]))
    return adj
for q in [3, 4, 5]:
    F = GF(q); E = list(F.elts())
    ellpts = [(0, 1, 0)] + [norm(F, (0, t, 1)) for t in E]
    for combo in itertools.permutations(ellpts, 4):
        hats = dict(zip(['a', 't0', 't1', 'tc'], combo))
        G = build_free(q, hats)
        degs = sorted(set(len(G[v]) for v in G))
        assert diameter(G) == 3 and bip(G) and len(G) == 2 * (q*q + q + 6) and degs[-1] == q + 2, (q, combo)
    print(f"q={q}: all {len(list(itertools.permutations(ellpts,4)))} ordered choices of 4 hat points on ell: order {2*(q*q+q+6)}, diameter 3, degrees {degs}")
