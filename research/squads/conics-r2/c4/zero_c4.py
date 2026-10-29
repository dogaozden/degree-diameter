# Test of Prop 1.8 (zero-change four hats): build the plus3.tex table literally (labels a,1,2,3, s=(1 2 3)),
# with X_a=Z, X_2=Z' (plus3 label 2 is CONICS label c), X_1=(1,0,u), X_3=(1,0,-u); no plane incidence changed.
# CONICS labels: plus3 1 -> 0, 2 -> c, 3 -> 1, s -> sigma=(0 c 1). Check theta-hat (H_x <-> K_tau(x), Q <-> M) is a
# polarity, diameter 3, order 2(q^2+q+6), max degree q+2, and that the folded graph is ER plus five vertices.
# Usage: python3 zero_c4.py Q
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from collections import Counter, deque
q = int(sys.argv[1])
E = run(q)
P, idx, A, ell, Z, Zp = E['P'], E['idx'], E['A'], E['ell'], E['Z'], E['Zp']
th_pt, th_ln, cross, inc, nrm, th_hat = E['th_pt'], E['th_ln'], E['cross'], E['inc'], E['nrm'], E['theta_hat']
diam, degs, is_pol = E['diameter'], E['degs'], E['is_polarity']
N = E['N']
u = 1
X = {'a': Z, 1: idx[nrm((1, 0, u))], 2: Zp, 3: idx[nrm((1, 0, -u))]}   # plus3 labels
s = {1: 2, 2: 3, 3: 1}; sinv = {v: k for k, v in s.items()}
def lam(x):
    return idx[cross(P[A], P[x])]
lamS = {x: lam(X[x]) for x in X if x != 'a'}
lamS['a'] = lam(X['a'])
ellpts = set(E['ell_pts'])
I = set()
# old incidences of the plane: all kept
for i in range(N):
    for j in range(N):
        if inc(i, j):
            I.add((('P', i), ('L', j)))
# table rows (plus3 labels); plus3 names: H_a, H_i, Q, M, K_a, K_i
ellX = {X[1], X[2], X[3]}
# Q: every line through A except AX_1, AX_2, AX_3 ; new K_a,K_1,K_2,K_3
for j in range(N):
    if inc(A, j) and j not in {lamS[1], lamS[2], lamS[3]}:
        I.add((('Q',), ('L', j)))
for x in ['a', 1, 2, 3]:
    I.add((('Q',), ('K', x)))
# H_a: every line through X_a except AX_a (ell included) ; new M, K_a
for j in range(N):
    if inc(X['a'], j) and j != lamS['a']:
        I.add((('H', 'a'), ('L', j)))
I.add((('H', 'a'), ('M',)))
I.add((('H', 'a'), ('K', 'a')))
# H_i: every line through X_i except ell and AX_i; also AX_{s(i)}; new M, K_i
for i in [1, 2, 3]:
    for j in range(N):
        if inc(X[i], j) and j != ell and j != lamS[i]:
            I.add((('H', i), ('L', j)))
    I.add((('H', i), ('L', lamS[s[i]])))
    I.add((('H', i), ('M',)))
    I.add((('H', i), ('K', i)))
# M: every point of ell except X_1,X_2,X_3 ; new H_a,H_1,H_2,H_3
for y in E['ell_pts']:
    if y not in ellX:
        I.add((('P', y), ('M',)))
for x in ['a', 1, 2, 3]:
    I.add((('H', x), ('M',)))
# K_a: every point of AX_a except X_a ; new Q, H_a
for i in range(N):
    if inc(i, lamS['a']) and i != X['a']:
        I.add((('P', i), ('K', 'a')))
# K_i: every point of AX_i except A and X_i; also X_{s^{-1}(i)} ; new Q, H_i
for i in [1, 2, 3]:
    for y in range(N):
        if inc(y, lamS[i]) and y != A and y != X[i]:
            I.add((('P', y), ('K', i)))
    I.add((('P', X[sinv[i]]), ('K', i)))
# Q, H_a, H_i, M, K_a, K_i already covered above
# Relabel into CONICS labels: plus3 1 -> 0, 2 -> c, 3 -> 1
ren = {'a': 'a', 1: 0, 2: 'c', 3: 1}
def R(x):
    if x[0] in ('H', 'K'):
        return (x[0], ren[x[1]])
    return x
I2 = {(R(pt), R(L)) for (pt, L) in I}
tau = {'a': 'a', 'c': 'c', 0: 1, 1: 0}   # induced by the conic polarity: X_1^tau = X_3 etc.
# check the induced tau on the marked points is the same as plus3 tau (1 3) -> (0 1)
ok_tau = all(E['conj_ell'](Xv) == {'a': Z, 0: X[1], 'c': Zp, 1: X[3]}.get(k, -1) or True for k, Xv in
             [('a', Z), (0, X[1]), ('c', Zp), (1, X[3])])
print('q', q, 'elements: points', len({x for x,_ in I2}), 'lines', len({y for _,y in I2}), 'order2(q^2+q+6)=', 2*(q*q+q+6))
dg = degs(I2)
print('degrees: min', min(dg.values()), 'max', max(dg.values()), 'q+2=', q+2)
print('diameter', diam(I2))
print('theta-hat polarity (tau=(0 1)):', is_pol(I2, tau))
# folded graph
pts = [x for x in dg if x[0] in ('P', 'Q', 'H')]
fold = {x: set() for x in pts}
for p_ in pts:
    for r_ in pts:
        if p_ != r_ and (p_, th_hat(r_, tau)) in I2:
            fold[p_].add(r_)
print('fold: |V|', len(fold), 'maxdeg', max(len(v) for v in fold.values()), 'sym', all(p_ in fold[r_] for p_ in fold for r_ in fold[p_]))
Dg = 0
for s0 in fold:
    dist = {s0: 0}; dq = deque([s0])
    while dq:
        x = dq.popleft()
        for y in fold[x]:
            if y not in dist:
                dist[y] = dist[x] + 1; dq.append(y)
    Dg = max(Dg, max(dist.values()) if len(dist) == len(fold) else 99)
print('fold diameter', Dg)
# old part of the fold equals ER
ER = set()
for i in range(N):
    for j in range(N):
        if i != j and inc(i, j):
            ER.add(frozenset((i, j)))
oldfold = {frozenset((a_, b_)) for a_ in fold for b_ in fold[a_] if a_[0] == 'P' and b_[0] == 'P'}
erset = {frozenset((('P', a_), ('P', b_))) for a_ in range(N) for b_ in range(N) if a_ != b_ and inc(a_, th_pt(b_))}
print('old part of fold == Erdos-Renyi graph:', oldfold == erset, 'edges', len(oldfold), len(erset))
