# Independent check (card c4, squad conics-r2) of research/synthetic/CONICS.md sections 0-1.
# Written from the definitions in research/squads/conics-r1/BRIEF.md and SYNTHETIC.md Definition 1.1.
# Prime q only (q = 5, 7, 11, 13). Usage: python3 check_c4.py Q [mode]
import itertools, sys
from collections import deque

def run(q, mode=None):
    p = q
    inv2 = pow(2, p - 2, p)

    def nrm(v):
        v = tuple(c % p for c in v)
        x = next(c for c in v if c != 0)
        k = pow(x, p - 2, p)
        return tuple((c * k) % p for c in v)

    trip = sorted({nrm(v) for v in itertools.product(range(p), repeat=3) if any(v)})
    N = len(trip)
    assert N == p * p + p + 1
    idx = {v: i for i, v in enumerate(trip)}
    P = trip  # points and lines are both indexed by normalized triples

    def inc(i, j):
        return sum(a * b for a, b in zip(P[i], P[j])) % p == 0

    def cross(u, v):
        return nrm((u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0]))

    # conic x z = y^2 ; polarity point (x,y,z) -> line [z,-2y,x], line [a,b,c] -> point (c,-b/2,a)
    def th_pt(i):  # point index -> line index
        x, y, z = P[i]
        return idx[nrm((z, (-2 * y) % p, x))]

    def th_ln(j):  # line index -> point index
        a, b, c = P[j]
        return idx[nrm((c, (-b * inv2) % p, a))]

    def on_conic(i):
        x, y, z = P[i]
        return (x * z - y * y) % p == 0

    # sanity: polarity
    for i in range(N):
        assert th_ln(th_pt(i)) == i
        for j in range(N):
            # p I L  <=>  theta(L) I theta(p)
            assert inc(i, j) == inc(th_ln(j), th_pt(i)), "polarity fails"
    # frame: A = (0,1,0), ell = theta(A) = [0,1,0]
    A = idx[(0, 1, 0)]
    ell = th_pt(A)
    assert not on_conic(A) and P[ell] == (0, 1, 0)
    Z = idx[(1, 0, 0)]; Zp = idx[(0, 0, 1)]
    assert on_conic(Z) and on_conic(Zp)
    ell_pts = [i for i in range(N) if inc(i, ell)]
    assert len(ell_pts) == p + 1
    def conj_ell(i):  # X^tau = theta(X) ∩ ell
        L = th_pt(i)
        return idx[cross(P[L], P[ell])]

    def build(lab_pt, a, T, pi, rho):
        """lab_pt: dict label -> point index on ell (the marked points X_s).
        Returns (elements incidence set I, tau dict) or None if marked set not tau-invariant."""
        S = list(lab_pt.keys())
        X = lab_pt
        lam = {s: idx[cross(P[A], P[X[s]])] for s in S}
        # induced tau on labels
        tau = {}
        inv_map = {X[s]: s for s in S}
        for s in S:
            Y = conj_ell(X[s])
            if Y not in inv_map:
                return None
            tau[s] = inv_map[Y]
        ellstar = [i for i in ell_pts if i not in {X[t] for t in T}]
        Lamstar = [j for j in range(N) if inc(A, j) and j not in {lam[t] for t in T}]
        I = set()
        delete = {(X[s], lam[s]) for s in S}
        add = {(X[t], lam[rho[t]]) for t in T}
        for i in range(N):
            for j in range(N):
                if inc(i, j) and (i, j) not in delete:
                    I.add((('P', i), ('L', j)))
        for (i, j) in add:
            I.add((('P', i), ('L', j)))
        # R2
        for s in S:
            for j in range(N):
                if inc(X[s], j) and j != ell:
                    I.add((('H', s), ('L', j)))
        # R3
        for s in S:
            for i in range(N):
                if inc(i, lam[s]) and i != A:
                    I.add((('P', i), ('K', s)))
        # R4
        for i in ellstar:
            I.add((('P', i), ('M',)))
        for s in S:
            I.add((('H', s), ('M',)))
        # R5
        for j in Lamstar:
            I.add((('Q',), ('L', j)))
        for s in S:
            I.add((('Q',), ('K', s)))
        # R6
        I.add((('P', A), ('K', a)))
        I.add((('H', a), ('L', ell)))
        for t in T:
            I.add((('H', t), ('K', pi[t])))
        return I, tau, S

    def theta_hat(x, tau):
        k = x[0]
        if k == 'P': return ('L', th_pt(x[1]))
        if k == 'L': return ('P', th_ln(x[1]))
        if k == 'H': return ('K', tau[x[1]])
        if k == 'K': return ('H', tau[x[1]])
        if k == 'Q': return ('M',)
        if k == 'M': return ('Q',)
        raise ValueError(x)

    def is_polarity(I, tau):
        for (pt, L) in I:
            img = (theta_hat(L, tau), theta_hat(pt, tau))
            if img not in I:
                return False
            if theta_hat(theta_hat(pt, tau), tau) != pt:
                return False
        return True

    def elements(I):
        pts = set(); lns = set()
        for (pt, L) in I:
            pts.add(pt); lns.add(L)
        return pts, lns

    def adjacency(I):
        nb = {}
        for (pt, L) in I:
            nb.setdefault(pt, set()).add(L)
            nb.setdefault(L, set()).add(pt)
        return nb

    def diameter(I):
        nb = adjacency(I)
        els = list(nb.keys())
        D = 0
        for e in els:
            dist = {e: 0}; dq = deque([e])
            while dq:
                x = dq.popleft()
                for y in nb[x]:
                    if y not in dist:
                        dist[y] = dist[x] + 1; dq.append(y)
            if len(dist) != len(els):
                return None
            D = max(D, max(dist.values()))
        return D

    def degs(I):
        nb = adjacency(I)
        return {e: len(v) for e, v in nb.items()}

    return dict(N=N, P=P, idx=idx, A=A, ell=ell, Z=Z, Zp=Zp, ell_pts=ell_pts, build=build,
                theta_hat=theta_hat, is_polarity=is_polarity, elements=elements,
                adjacency=adjacency, diameter=diameter, degs=degs, th_pt=th_pt, th_ln=th_ln,
                on_conic=on_conic, cross=cross, inc=inc, nrm=nrm, conj_ell=conj_ell)

if __name__ == '__main__':
    q = int(sys.argv[1])
    env = run(q, 'all')
    print('q', q, 'points', env['N'], 'sanity ok')
