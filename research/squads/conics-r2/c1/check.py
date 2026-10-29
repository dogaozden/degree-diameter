"""conics-r2 card c1: independent check of CONICS.md Prop 1.8 (self-polar four hats on an unchanged plane).

Written from the claim as stated in the card brief; does not import research/synthetic/conics/.
Only GF(q) arithmetic is taken from research/plus2/coords/coords.py (class GF).

Usage: python check.py [--out results.json]
"""
import sys, itertools, json
sys.path.insert(0, '/home/user/degree-diameter/research/plus2/coords')
from coords import GF
import numpy as np
import networkx as nx


def run_instance(q, u, F, tau_identity=False):
    add, mul, neg, inv = F.add, F.mul, F.neg, F.inv
    two = add(1, 1)
    half = inv(two)

    def normalize(v):
        for t in v:
            if t != 0:
                s = inv(t)
                return tuple(mul(s, w) for w in v)
        raise ValueError("zero vector")

    def dot(a, b):
        return add(add(mul(a[0], b[0]), mul(a[1], b[1])), mul(a[2], b[2]))

    def cross(a, b):
        return (add(mul(a[1], b[2]), neg(mul(a[2], b[1]))),
                add(mul(a[2], b[0]), neg(mul(a[0], b[2]))),
                add(mul(a[0], b[1]), neg(mul(a[1], b[0]))))

    # points and lines of PG(2,q): normalized triples (same index set for both)
    trip = sorted({normalize(v) for v in itertools.product(range(q), repeat=3) if any(v)})
    N = len(trip)
    assert N == q * q + q + 1
    idx = {t: i for i, t in enumerate(trip)}
    T = N + 5  # + Q, H_a, H_1, H_2, H_3 (points); M, K_a, K_1, K_2, K_3 (lines)

    # labels for new points / lines
    NP = {'Q': N + 0, 'a': N + 1, '1': N + 2, '2': N + 3, '3': N + 4}   # new points
    NL = {'M': N + 0, 'a': N + 1, '1': N + 2, '2': N + 3, '3': N + 4}   # new lines

    # the frame
    A = (0, 1, 0)
    Xp = {'a': (1, 0, 0), '2': (0, 0, 1), '1': (1, 0, u), '3': (1, 0, neg(u))}
    ell = normalize((0, 1, 0))
    AX = {k: normalize(cross(A, Xp[k])) for k in 'a123'}
    s = {'1': '2', '2': '3', '3': '1'}
    sinv = {v: k for k, v in s.items()}
    tau = {'a': 'a', '1': '3', '2': '2', '3': '1'}
    if tau_identity:
        tau = {k: k for k in 'a123'}

    # sanity: the conic and the polarity
    def polar_pt(p):   # point (x,y,z) -> line [z,-2y,x]
        return normalize((p[2], neg(mul(two, p[1])), p[0]))

    def pole_ln(L):    # line [a,b,c] -> point (c,-b/2,a)
        return normalize((L[2], neg(mul(L[1], half)), L[0]))

    # old incidence (all kept)
    inc = np.zeros((T, T), dtype=bool)
    for i, p in enumerate(trip):
        for j, L in enumerate(trip):
            if dot(p, L) == 0:
                inc[i, j] = True

    # ---- point-side specs: new point -> old lines, new lines (pairs collected for cross-check)
    pt_side_nn = set()
    def add_pt_spec(lab, old_lines, new_lines):
        for L in old_lines:
            inc[NP[lab], idx[L]] = True
        for K in new_lines:
            inc[NP[lab], NL[K]] = True
            pt_side_nn.add((lab, K))

    lines_thru_A = [L for L in trip if dot(A, L) == 0]
    add_pt_spec('Q', [L for L in lines_thru_A if L not in (AX['1'], AX['2'], AX['3'])], ['a', '1', '2', '3'])
    add_pt_spec('a', [L for L in trip if dot(Xp['a'], L) == 0 and L != AX['a']], ['M', 'a'])
    for i in '123':
        old = [L for L in trip if dot(Xp[i], L) == 0 and L != ell and L != AX[i]]
        old.append(AX[s[i]])
        add_pt_spec(i, old, ['M', i])

    # ---- line-side specs: new line -> old points, new points (collected for cross-check)
    ln_side_nn = set()
    def add_ln_spec(lab, old_pts, new_pts):
        for p in old_pts:
            inc[idx[p], NL[lab]] = True
        for Pn in new_pts:
            inc[NP[Pn], NL[lab]] = True
            ln_side_nn.add((Pn, lab))

    on_ell = [p for p in trip if dot(p, ell) == 0]
    add_ln_spec('M', [p for p in on_ell if p not in (Xp['1'], Xp['2'], Xp['3'])], ['a', '1', '2', '3'])
    add_ln_spec('a', [p for p in trip if dot(p, AX['a']) == 0 and p != Xp['a']], ['Q', 'a'])
    for i in '123':
        pts = [p for p in trip if dot(p, AX[i]) == 0 and p not in (A, Xp[i])]
        pts.append(Xp[sinv[i]])
        add_ln_spec(i, pts, ['Q', i])

    # the new-new incidences: point-side and line-side specs must agree
    assert pt_side_nn == ln_side_nn, (pt_side_nn ^ ln_side_nn)
    # point-side new-new flags were written only from pt specs; line-side from ln specs; both written: fine

    # ---- theta
    theta_pt = np.zeros(T, dtype=int)   # point index -> line index
    theta_ln = np.zeros(T, dtype=int)   # line index -> point index
    for i, p in enumerate(trip):
        theta_pt[i] = idx[polar_pt(p)]
    for j, L in enumerate(trip):
        theta_ln[j] = idx[pole_ln(L)]
    # new points -> new lines, new lines -> new points
    theta_pt[NP['Q']] = NL['M']
    theta_ln[NL['M']] = NP['Q']
    for x in 'a123':
        theta_pt[NP[x]] = NL[tau[x]]
        theta_ln[NL[x]] = NP[tau[x]]
    # ----- check (1): degrees
    rs = inc.sum(axis=1)
    cs = inc.sum(axis=0)
    maxdeg = int(max(rs.max(), cs.max()))
    mindeg = int(min(rs.min(), cs.min()))
    deg_ok = (maxdeg == q + 2)   # claim (1) is the maximum degree; deficient (degree q+1) elements are allowed
    n_def_pt = int((rs == q + 1).sum())
    n_def_ln = int((cs == q + 1).sum())

    # ----- check (2): diameter 3 of the incidence graph
    C = inc.astype(np.int64)
    pp = C @ C.T
    ll = C.T @ C
    off = ~np.eye(T, dtype=bool)
    share_ok = bool((pp[off] > 0).all()) and bool((ll[off] > 0).all())
    G = nx.Graph()
    G.add_nodes_from([('p', i) for i in range(T)] + [('l', j) for j in range(T)])
    for i, j in zip(*np.nonzero(inc)):
        G.add_edge(('p', int(i)), ('l', int(j)))
    diam = nx.diameter(G)
    diam_ok = share_ok and diam == 3

    # ----- check (3): theta is a polarity of S and maps flags to flags
    inv_ok = bool((theta_ln[theta_pt] == np.arange(T)).all()) and bool((theta_pt[theta_ln] == np.arange(T)).all())
    # T_mat[i,j] = inc[theta(line j), theta(point i)]
    Tmat = inc[np.ix_(theta_ln, theta_pt)].T
    flag_ok = bool((Tmat == inc).all())
    polar_ok = inv_ok and flag_ok

    # ----- check (4): folded graph on all points of S
    Adj = inc[:, theta_pt].copy()     # Adj[p, r] = p on theta(r)
    np.fill_diagonal(Adj, False)
    sym_ok = bool((Adj == Adj.T).all())
    fdeg = Adj.sum(axis=1)
    fold_maxdeg = int(fdeg.max())
    Ai = Adj.astype(np.int64)
    reach = Adj | ((Ai @ Ai) > 0) | np.eye(T, dtype=bool)
    fold_diam2 = bool(reach.all()) and not bool(Adj[off].all())
    nverts = T
    # Erdos-Renyi graph computed from the bilinear form B(p,r) = p1 r3 + p3 r1 - 2 p2 r2 directly
    ER = np.zeros((N, N), dtype=bool)
    for i, p in enumerate(trip):
        for j, r in enumerate(trip):
            if i != j:
                b = add(add(mul(p[0], r[2]), mul(p[2], r[0])), neg(mul(two, mul(p[1], r[1]))))
                ER[i, j] = (b == 0)
    old_ok = bool((Adj[:N, :N] == ER).all())
    fold_ok = sym_ok and fold_maxdeg <= q + 2 and fold_diam2 and nverts == q * q + q + 6 and old_ok

    return dict(q=q, u=u, N=N, T=T, maxdeg=maxdeg, mindeg=mindeg, deg_ok=deg_ok, n_def_pt=n_def_pt, n_def_ln=n_def_ln,
                inc_diam=diam, share_ok=share_ok, diam_ok=diam_ok,
                inv_ok=inv_ok, flag_ok=flag_ok, polar_ok=polar_ok,
                fold_sym=sym_ok, fold_maxdeg=fold_maxdeg, fold_diam2=fold_diam2,
                fold_nverts=nverts, old_is_ER=old_ok, fold_ok=fold_ok,
                all_pass=bool(deg_ok and diam_ok and polar_ok and fold_ok))


def main():
    out = None
    if '--out' in sys.argv:
        out = sys.argv[sys.argv.index('--out') + 1]
    rows, controls = [], []
    for q in [3, 5, 7, 9, 11, 13]:
        F = GF(q)
        us = [u for u in range(1, q) if F.neg(u) != u]
        for u in us:
            r = run_instance(q, u, F)
            rows.append(r)
            c = run_instance(q, u, F, tau_identity=True)
            controls.append({'q': q, 'u': u, 'polar_ok': c['polar_ok'], 'inv_ok': c['inv_ok'], 'flag_ok': c['flag_ok'],
                             'deg_ok': c['deg_ok'], 'diam_ok': c['diam_ok'], 'fold_ok': c['fold_ok']})
            print(f"q={q:2d} u={u:2d} deg={r['maxdeg']}/{r['mindeg']} def={r['n_def_pt']}/{r['n_def_ln']} inc_diam={r['inc_diam']} share={r['share_ok']} "
                  f"polar={r['polar_ok']}(inv={r['inv_ok']},flag={r['flag_ok']}) fold_maxdeg={r['fold_maxdeg']} "
                  f"fold_diam2={r['fold_diam2']} n={r['fold_nverts']} oldER={r['old_is_ER']} PASS={r['all_pass']} | "
                  f"control polar_ok={c['polar_ok']} flag_ok={c['flag_ok']}", flush=True)
    score = sum(r['all_pass'] for r in rows)
    ctrl_fail_all = all(not c['polar_ok'] for c in controls)
    summary = dict(instances=len(rows), score=score, control_polar_fails_in=sum(not c['polar_ok'] for c in controls),
                   control_instances=len(controls), valid=bool(score == len(rows) and ctrl_fail_all))
    print(json.dumps(summary))
    if out:
        with open(out, 'w') as f:
            json.dump({'rows': rows, 'controls': controls, 'summary': summary}, f, indent=1)


if __name__ == '__main__':
    main()
