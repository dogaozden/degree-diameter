# (a) Remark 1.5 counterexample: four-hat labelled frame with X_a=Z', X_0=Z, X_c=(1,0,1), X_1=(1,0,-1) at q=5,7.
#     Lemma 1.3 applies with the induced tau=(c 1); check theta-hat polarity, counts, diameter, fold diameter.
# (b) Completed structure of Prop 1.9: is the folded graph regular, and of diameter 2?
# Usage: python3 cex_c4.py Q
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from collections import deque
q = int(sys.argv[1])
E = run(q)
P, idx, A, ell, Z, Zp = E['P'], E['idx'], E['A'], E['ell'], E['Z'], E['Zp']
build, is_pol, diam, degs, th_hat, nrm = E['build'], E['is_polarity'], E['diameter'], E['degs'], E['theta_hat'], E['nrm']
PI4 = {0: 'c', 'c': 1, 1: 0}; RHO4 = {0: 'c', 'c': 1, 1: 0}; T4 = [0, 'c', 1]
def fold_of(I, tau):
    pts = [x for x in degs(I) if x[0] in ('P', 'Q', 'H')]
    F = {x: set() for x in pts}
    for p_ in pts:
        for r_ in pts:
            if p_ != r_ and (p_, th_hat(r_, tau)) in I:
                F[p_].add(r_)
    return F
def fold_diam(F):
    D = 0
    for s0 in F:
        dist = {s0: 0}; dq = deque([s0])
        while dq:
            x = dq.popleft()
            for y in F[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; dq.append(y)
        if len(dist) != len(F): return None
        D = max(D, max(dist.values()))
    return D
fr = {'a': Zp, 0: Z, 'c': idx[nrm((1, 0, 1))], 1: idx[nrm((1, 0, -1))]}
I, tau, S = build(fr, 'a', T4, PI4, RHO4)
print('q', q, 'counterexample frame: tau =', tau, 'polarity:', is_pol(I, tau),
      'points', len({x for x, _ in I if x[0] in ('P','Q','H')}), 'diam', diam(I))
F = fold_of(I, tau)
print('  fold: |V| =', len(F), 'maxdeg', max(len(v) for v in F.values()), 'diam', fold_diam(F))
# (b) completion as in Prop 1.9 for the standard frame u=1
fr = {'a': Z, 0: idx[nrm((1, 0, 1))], 'c': Zp, 1: idx[nrm((1, 0, -1))]}
I, tau, S = build(fr, 'a', T4, PI4, RHO4)
dg = degs(I)
X = fr
marked = set(X.values())
defP = [x[1] for x in dg if x[0] == 'P' and dg[x] == q + 1]
mu = {}
for p in defP:
    if not E['on_conic'](p):
        mu[p] = E['th_pt'](p)
    else:
        L = idx[E['cross'](P[A], P[p])]
        cp = [x for x in range(E['N']) if E['on_conic'](x) and E['inc'](x, L) and x != p]
        mu[p] = E['th_pt'](cp[0])
I2 = set(I)
for p, L in mu.items():
    I2.add((('P', p), ('L', L)))
F2 = fold_of(I2, tau)
degF = sorted(set(len(v) for v in F2.values()))
absS = [x for x in F2 if x[0] == 'P' and (x, ('L', E['th_pt'](x[1]))) in I2]
print('completed: diam', diam(I2), 'self-polar', is_pol(I2, tau), 'fold degrees', degF,
      'fold diam', fold_diam(F2), 'absolute points of S (loops in fold):', len(absS))
print('  fold degree of absolute point', [len(F2[x]) for x in absS][:5], 'vs q+2 =', q+2)
# (c) general fact: S diam<=3 iff every two points have a common neighbour in the fold with loops at absolute points
def loops_ok(F, I2):
    ok = True
    for a_ in F:
        for b_ in F:
            if a_ == b_: continue
            common = set(F[a_]) & set(F[b_])
            if (a_, th_hat(a_, tau)) in I2: common.add(a_)
            if (b_, th_hat(b_, tau)) in I2: common.add(b_)
            if not common: ok = False
    return ok
print('  S diam<=3 (completed):', diam(I2) <= 3, ' loop-convention common-neighbour property:', loops_ok(F2, I2))
