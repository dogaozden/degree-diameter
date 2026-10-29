# Tests: Prop 1.6 (corrected flag test), Prop 1.9 (explicit completion mu), Cor 1.7 fold description.
# Usage: python3 prop19_c4.py Q
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from collections import Counter, deque
q = int(sys.argv[1])
E = run(q)
P, idx, A, ell, Z, Zp = E['P'], E['idx'], E['A'], E['ell'], E['Z'], E['Zp']
build, is_pol, diam, degs, adj = E['build'], E['is_polarity'], E['diameter'], E['degs'], E['adjacency']
th_pt, th_ln, on_conic, cross, inc, nrm, th_hat = E['th_pt'], E['th_ln'], E['on_conic'], E['cross'], E['inc'], E['nrm'], E['theta_hat']
N = E['N']
PI4 = {0: 'c', 'c': 1, 1: 0}; RHO4 = {0: 'c', 'c': 1, 1: 0}
T4 = [0, 'c', 1]
PI3 = {0: 1, 1: 0}; RHO3 = {0: 0, 1: 1}; T3 = [0, 1]
bad = Counter(); report = []
frame_bad = None

def frame(u, four):
    X0 = idx[nrm((1, 0, u))]; X1 = idx[nrm((1, 0, -u))]
    d = {'a': Z, 0: X0, 1: X1}
    if four: d['c'] = Zp
    return d

def lam(X):
    return idx[cross(P[A], P[X])]

def PiFlag(i, j):  # flag of the plane (not of S)
    return inc(i, j)

for u in range(1, q):
  for four in (True, False):
    fr = frame(u, four)
    T, PI, RHO = (T4, PI4, RHO4) if four else (T3, PI3, RHO3)
    I, tau, S = build(fr, 'a', T, PI, RHO)
    X = fr
    before = sum(bad.values())
    lamS = {s: lam(X[s]) for s in S}
    # ---------- Prop 1.6, corrected
    if four:
        # (1) deleted flags (X_s, lam_s) are Pi-flags not in S, for s in S
        for s in S:
            if not PiFlag(X[s], lamS[s]) or (('P', X[s]), ('L', lamS[s])) in I:
                bad['1.6(1) deleted flag not a deleted Pi-flag'] += 1
        # conjugate pairs among marked points (Pi)
        # (2) rotation flags are in S: (X0,lam_c), (Xc,lam_1), (X1,lam_0)
        for (t, r) in [(0, 'c'), ('c', 1), (1, 0)]:
            if (('P', X[t]), ('L', lamS[r])) not in I:
                bad['1.6(2) rotation flag missing'] += 1
        # X0 ~ Z' (two flags), X1 absolute in S
        if not ((('P', X[0]), ('L', lamS['c'])) in I and (('P', X['c']), ('L', lamS[1])) in I):
            bad['1.6(2) X0-Z conj'] += 1
        if (('P', X[1]), ('L', lamS[0])) not in I:
            bad['1.6(2) X1 absolute'] += 1
        # (3) links: H0-Hc (two flags: H0 I K_c, Hc I K_1); H1 absolute (H1 I K_0); A I K_a; H_a I ell
        if not ((('H', 0), ('K', 'c')) in I and (('H', 'c'), ('K', 1)) in I and (('H', 1), ('K', 0)) in I):
            bad['1.6(3) links'] += 1
        if not ((('P', A), ('K', 'a')) in I and (('H', 'a'), ('L', ell)) in I):
            bad['1.6(3) A-Ha'] += 1
        # (4) Q conjugate to every H_s (Q I K_s), to Z (Q I lam_a), unmarked ell points
        for s in S:
            if (('Q',), ('K', s)) not in I:
                bad['1.6(4) Q-H_s'] += 1
        unmarked = [y for y in E['ell_pts'] if y not in set(X.values())]
        for y in unmarked + [Z]:
            if (('Q',), ('L', lamS['a'] if False else idx[cross(P[A], P[y])] if False else th_pt(y))) not in I:
                bad['1.6(4) Q-unmarked/Z'] += 1
        # H_s conjugates in Pi: the q points of lam_{tau s} other than A; for s=a it is all q+1 points incl. A
        for s in S:
            conj = {th_ln(j) for j in range(N) if (('H', s), ('L', j)) in I}
            target = {i for i in range(N) if inc(i, lam(X[tau[s]]))}
            if s == 'a':
                if conj != target:
                    bad['1.6(4) H_a conj'] += 1
                if A not in conj:
                    bad['1.6(4) A not conj to H_a (contradicts (3))'] += 1
                if len(conj) != q + 1:
                    bad['1.6(4) H_a conj count'] += 1
            else:
                if conj != target - {A}:
                    bad['1.6(4) H_s conj (s!=a)'] += 1
    # ---------- Prop 1.9 completion
    dg = degs(I)
    defP = sorted([x[1] for x in dg if x[0] == 'P' and dg[x] == q + 1])
    defL = sorted([th_ln(x[1]) for x in dg if x[0] == 'L' and dg[x] == q + 1])  # as points via theta, for matching
    defLines = sorted([x[1] for x in dg if x[0] == 'L' and dg[x] == q + 1])
    if len(defP) != len(defLines):
        bad['1.9 counts'] += 1
    mu = {}
    for p in defP:
        if not on_conic(p):
            mu[p] = th_pt(p)                      # line index of p^perp
        else:
            # p* = second point of C on line Ap
            Lap = lam_p = idx[cross(P[A], P[p])]
            cpts = [x for x in range(N) if on_conic(x) and inc(x, Lap)]
            others = [x for x in cpts if x != p]
            if len(cpts) != 2 or len(others) != 1:
                bad['1.9 Ap meets C in 2 points (p on C)'] += 1
                continue
            ps = others[0]
            if inc(ps, ell):
                bad['1.9 p* on ell'] += 1
            mu[p] = th_pt(ps)                     # (p*)^perp, tangent at p*
    if sorted(mu.values()) != defLines:
        bad['1.9 mu is not a bijection onto deficient lines'] += 1
    for p, L in mu.items():
        if inc(p, L):
            bad['1.9 p I mu(p)'] += 1
    I2 = set(I)
    for p, L in mu.items():
        I2.add((('P', p), ('L', L)))
    dg2 = degs(I2)
    if any(dg2[x] != q + 2 for x in dg2):
        bad['1.9 not (q+2)-regular'] += 1
    D2 = diam(I2)
    if D2 != 3:
        bad['1.9 diameter after completion != 3 (got %s)' % D2] += 1
    if not is_pol(I2, tau):
        bad['1.9 completed structure not self-polar'] += 1
    # added flags: mu-flags for p on C are loops? check what folding gives
    loops = [p for p, L in mu.items() if L == th_pt(p) and False]
    # absolute points after completion: folded degree
    absP = [x for x in dg2 if x[0] == 'P' and inc(x[1], th_pt(x[1]))]
    gdeg = Counter()
    for x in dg2:
        if x[0] in ('P', 'Q', 'H'):
            gdeg[x] = sum(1 for L in [y for (pp, y) in I2 if pp == x] if L[0] != 'M' or True) 
    absS = [x for x in dg2 if x[0] == 'P' and (x, ('L', th_pt(x[1]))) in I2]
    report.append((u, 'four' if four else 'three', 'deficient pts', len(defP), 'new failures', sum(bad.values()) - before,
                   'diam(completed)', D2, 'S-absolute points after completion', len(absS)))
    # Cor 1.7 fold description (four hats only)
    if four:
        th = th_hat
        # old part of fold = ER minus {X0,X1} plus {X0,Z'}
        ER = set()
        for i in range(N):
            for j in range(N):
                if i != j and inc(i, th_pt(j)):
                    ER.add(frozenset((i, j)))
        fold = set()
        pts = [x for x in dg if x[0] in ('P', 'Q', 'H')]
        for p_ in pts:
            for r_ in pts:
                if p_ != r_ and (p_, th(r_, tau)) in I:
                    fold.add(frozenset((p_, r_)))
        oldfold = {e for e in fold if all(x[0] == 'P' for x in e)}
        oldER = {frozenset(((('P', a_)), ('P', b_))) for a_, b_ in [tuple(e) for e in ER]}
        X0, X1, Zp_ = ('P', X[0]), ('P', X[1]), ('P', Zp)
        expect_old = (oldER - {frozenset((X0, X1))}) | {frozenset((X0, Zp_))}
        if oldfold != expect_old:
            bad['Cor1.7 old part is not ER - X0X1 + X0Z\''] += 1
        Qn = {next(iter(e - {('Q',)})) for e in fold if ('Q',) in e}
        exp_Qn = {('P', Z)} | {('P', y) for y in E['ell_pts'] if y not in set(X.values())} | {('H', s) for s in S}
        if Qn != exp_Qn:
            bad['Cor1.7 nbrs of Q'] += 1
        for s in S:
            Hn = {next(iter(e - {('H', s)})) for e in fold if ('H', s) in e}
            Pn = {x for x in Hn if x[0] == 'P'}
            Hs = {x for x in Hn if x[0] == 'H'}
            want = {('P', i) for i in range(N) if inc(i, lam(X[tau[s]])) and i != A}
            if s == 'a':
                want = want | {('P', A)}
            if Pn != want:
                bad['Cor1.7 nbrs of H_%s in Pi' % s] += 1
    # zero-change check left to zero_c4.py
print('FAILS' if bad else 'no failures')
for k, v in bad.items():
    print('  FAIL', v, k)
for r in report:
    print(r)
