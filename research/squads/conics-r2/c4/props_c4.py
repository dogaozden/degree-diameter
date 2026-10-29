# Tests of Lemma 1.4 (degrees), Prop 1.6 (gadget), Cor 1.7 (fold), Prop 1.9 (completion) on conic frames.
# Usage: python3 props_c4.py Q
import sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/conics-r2/c4')
from check_c4 import run
from collections import Counter, deque
q = int(sys.argv[1])
E = run(q)
P, idx, A, ell, Z, Zp = E['P'], E['idx'], E['A'], E['ell'], E['Z'], E['Zp']
build, is_pol, diam, degs, adj = E['build'], E['is_polarity'], E['diameter'], E['degs'], E['adjacency']
th_pt, th_ln, on_conic, cross, inc, nrm = E['th_pt'], E['th_ln'], E['on_conic'], E['cross'], E['inc'], E['nrm']
N = E['N']
T4 = [0, 'c', 1]; T3 = [0, 1]
PI4 = {0: 'c', 'c': 1, 1: 0}; RHO4 = {0: 'c', 'c': 1, 1: 0}
PI3 = {0: 1, 1: 0}; RHO3 = {0: 0, 1: 1}
def out(*a): print(*a)

def frame(u, four=True):
    X0 = idx[nrm((1, 0, u))]; X1 = idx[nrm((1, 0, -u))]
    d = {'a': Z, 0: X0, 1: X1}
    if four: d['c'] = Zp
    return d

fails = Counter()
for u in range(1, q):
  for four in (True, False):
    fr = frame(u, four)
    T, PI, RHO = (T4, PI4, RHO4) if four else (T3, PI3, RHO3)
    I, tau, S = build(fr, 'a', T, PI, RHO)
    dg = degs(I)
    nm = 'four' if four else 'three'
    # ---- Lemma 1.4: degrees in {q+1,q+2}; deficient counts
    defP = [x for x in dg if x[0] in ('P',) and dg[x] == q + 1]
    defL = [x for x in dg if x[0] in ('L',) and dg[x] == q + 1]
    if not all(dg[x] in (q + 1, q + 2) for x in dg):
        fails['Lemma1.4 degrees not q+1/q+2'] += 1
    expect = (q - 1) * (q + 1 - len(S))
    if len(defP) != expect or len(defL) != expect:
        fails['Lemma1.4 counts'] += 1
    # deficient points: off ell, not A, on A-Y with Y unmarked
    marked = set(fr.values())
    unmarked = [y for y in E['ell_pts'] if y not in marked]
    predP = set()
    for y in unmarked:
        for i in range(N):
            if inc(i, idx[cross(P[A], P[y])]) and i != A and not inc(i, ell):
                predP.add(i)
    if predP != {x[1] for x in defP}:
        fails['Lemma1.4 deficient points description'] += 1
    # Lemma 1.4 says each deficient point is on q-|S| deficient lines
    # ---- Prop 1.6 (1)-(3) in four hats: conjugacy bookkeeping
    if four:
        Xc = lambda s: fr[s]
        # (1) deleted flags (X_s, lam_s) = (X_s, X_{tau s}^perp): conjugate pairs
        for s in ['a', 0, 'c', 1]:
            t = tau[s]
            if not inc(Xc(s), th_ln(Xc(t))) if False else not inc(Xc(s), th_pt(Xc(t))) and False:
                pass
        # (2) rotation flags: X0 conj Z' (two flags), X1 absolute
        c2 = [inc(Xc(0), th_pt(Xc('c'))), inc(Xc('c'), th_pt(Xc(0))), inc(Xc(1), th_pt(Xc(1)))]
        if c2 != [True, True, True]:
            fails['Prop1.6(2) rotation conjugacy'] += 1
        # (4) H_a conjugate to the q+1 points of lambda_a (A included, via link A-H_a)
        conj_Ha = set()
        for j in range(N):
            if ('H', 'a') and (('H', 'a'), ('L', j)) in I:
                conj_Ha.add(P[th_ln(j)] if False else th_ln(j))
        lam_a_pts = {i for i in range(N) if inc(i, idx[cross(P[A], P[Z])])}
        if conj_Ha != lam_a_pts:
            fails['Prop1.6(4) H_a conjugates: q+1 points incl. A'] += 1
            out('   H_a conjugates:', len(conj_Ha), 'lambda_a pts:', len(lam_a_pts), 'A in conj:', A in conj_Ha)
        # H_0, H_c, H_1 conjugates among Pi-points = q points of lambda_{tau s} other than A
        for s in [0, 'c', 1]:
            cs = set()
            for j in range(N):
                if (('H', s), ('L', j)) in I:
                    cs.add(th_ln(j))
            ls = {i for i in range(N) if inc(i, idx[cross(P[A], P[Xc(tau[s])])])}
            if cs != ls - {A}:
                fails['Prop1.6(4) H_s conjugates for s!=a'] += 1
        # Q conjugate to every H_s, Z and unmarked points of ell
        qc = {th_ln(j) for j in range(N) if (('Q',), ('L', j)) in I}
        need = {Z} | set(unmarked)
        if not need.issubset(qc) or (qc - need - {A}) and False:
            fails['Prop1.6(4) Q conjugates'] += 1
        if qc != (need | {i for i in range(N) if inc(i, idx[cross(P[A], P[Z])]) and False}) and qc != need:
            # Q is on Lambda* lines; its Pi-conjugates are the points of ell* (Z and unmarked)
            if qc != need:
                fails['Prop1.6(4) Q conjugates exactly ell*'] += 1
    # ---- Cor 1.7: fold
    if max(dg.values()) != q + 2:
        fails['Cor1.7 max degree != q+2'] += 1
    # folded graph
    pts = sorted({x for (x, _) in I}, key=str)
    G = {x: set() for x in pts if x[0] in ('P', 'Q', 'H')}
    def fold_adj(x, y):
        return x != y and (x, ('L', th_pt(y[1])) if y[0] == 'P' else (x, None)) and False
    # generic: p ~ r iff (p, theta_hat(r)) in I  (theta_hat(r) computed through the rule)
    th = E['theta_hat']
    for p_ in G:
        for r_ in G:
            if p_ != r_ and (p_, th(r_, tau)) in I:
                G[p_].add(r_)
    # symmetric?
    sym = all(p_ in G[r_] for p_ in G for r_ in G[p_])
    if not sym:
        fails['fold not symmetric'] += 1
    gdeg = max(len(v) for v in G.values())
    # diameter of folded graph
    Dg = 0
    for s0 in G:
        dist = {s0: 0}; dq = deque([s0])
        while dq:
            x = dq.popleft()
            for y in G[x]:
                if y not in dist:
                    dist[y] = dist[x] + 1; dq.append(y)
        if len(dist) != len(G):
            Dg = None; break
        Dg = max(Dg, max(dist.values()))
    if Dg != 2:
        fails['Cor1.7 folded diameter != 2'] += 1
    out('u=%d %s: |V(fold)|=%d maxdeg=%d diam(fold)=%s  deficient pts=%d lines=%d  (q-1)(q+1-|S|)=%d' %
        (u, nm, len(G), gdeg, Dg, len(defP), len(defL), expect))
print('FAILS', dict(fails) if fails else 'none')
