"""Build the explicit graphs of Corollaries 10.1-10.4 from the printed ingredients only (Lemmas 1.1, 1.3, 1.4,
Prop. 6.4, Lemma 9.1, Definitions 2.1, 3.1), with random choices wherever the note says "any", and write an edge
list for bfs.c.  Usage: python3 families.py COR q r KB KA HUB OUT [seed] [variant]
  COR in {10.1, 10.2, 10.3, 10.4}; HUB = Y1:s | Y2:s | Y3:s:r' ; variant = 'plus1' frees one extra line on the
  D->H arcs that meets a line of the set (negative control, Theorem B predicts failure)."""
import sys, random, itertools
from gf import GF, normalize, span_points, proj_points
from gq import W, Q4, GQ, plucker

def lemma11_spread(F, Wq):
    al, be = F.irreducible_quadratic()
    m, a_ = F.mul, F.add
    out = [frozenset(Wq.idx[z] for z in span_points(F, (0, 0, 1, 0), (0, 0, 0, 1)))]
    for a in range(F.q):
        for b in range(F.q):
            out.append(frozenset(Wq.idx[z] for z in span_points(F, (1, 0, a, b), (0, 1, b, a_[m[al][a]][m[be][b]]))))
    lines = {frozenset(l): i for i, l in enumerate(Wq.lp)}
    S = [lines[l] for l in out]
    assert len(set(S)) == F.q ** 2 + 1
    cov = set().union(*[set(Wq.lp[i]) for i in S]); assert len(cov) == Wq.N      # a spread
    return S

def lemma13_partial_ovoid(F, Wq, rng):
    q = F.q; m = F.mul
    perp = lambda v: (F.neg[v[1]], v[0])
    a = [(1, 0), (0, 1), (1, 1)]
    b = [perp(a[(i - 1) % 3]) for i in range(3)]
    tau = rng.choice([t for t in range(q) if t not in (0, 1)])
    x = (1, tau)
    proj = lambda v: normalize(F, v)
    zs = [z for z in proj_points(F, 2) if z not in {proj(a[0]), proj(a[1]), proj(a[2]), proj(x)}]
    z = rng.choice(zs)
    pts = [(a[i][0], a[i][1], m[c][b[i][0]], m[c][b[i][1]]) for i in range(3) for c in range(1, q)]
    pts += [(x[0], x[1], 0, 0), (0, 0) + perp(z)]
    S = [Wq.idx[normalize(F, p)] for p in pts]
    assert len(set(S)) == 3 * q - 1
    assert all(b_ not in Wq.collinear[a_] for a_, b_ in itertools.combinations(S, 2))   # partial ovoid
    return S

def klein(F, Wq, Qq):
    """W-line i -> Q-point, W-point j -> Q-line (pencil), and check it is an isomorphism W^D -> Q"""
    lp = []
    for l in Wq.lp:
        P = plucker(F, Wq.coords[l[0]], Wq.coords[l[1]])
        lp.append(Qq.idx[normalize(F, (P[(0, 1)], P[(2, 3)], P[(0, 2)], P[(0, 3)], P[(1, 2)]))])
    qlines = {tuple(l): i for i, l in enumerate(Qq.lp)}
    pl = [qlines[tuple(sorted(lp[l] for l in Wq.pl[p]))] for p in range(Wq.N)]
    return lp, pl

def lemma14_duality(F, Wq):
    """psi: W-lines -> W-points, (p01,p03,p23,p12); phi: W-point x -> line {psi(l): x in l}"""
    psi = []
    for l in Wq.lp:
        P = plucker(F, Wq.coords[l[0]], Wq.coords[l[1]])
        psi.append(Wq.idx[normalize(F, (P[(0, 1)], P[(0, 3)], P[(2, 3)], P[(1, 2)]))])
    assert sorted(psi) == list(range(Wq.N))
    lines = {tuple(l): i for i, l in enumerate(Wq.lp)}
    phi = [lines[tuple(sorted(psi[l] for l in Wq.pl[x]))] for x in range(Wq.N)]
    for x in range(Wq.N):                      # x in l  <=>  psi(l) in phi(x)
        for l in range(Wq.N):
            assert (x in set(Wq.lp[l])) == (psi[l] in set(Wq.lp[phi[x]]))
    return psi, phi

def local_duality(G, src, rng):
    """Prop. 6.4: src='P' gives M: points -> lines, src='L' gives M: lines -> points; R = 2 elements"""
    N = G.N
    G2s = G.collinear if src == 'P' else G.meets
    G2t = G.meets if src == 'P' else G.collinear
    while True:
        x, y = rng.sample(range(N), 2)
        if y not in G2s[x]:
            break
    while True:
        l, m = rng.sample(range(N), 2)
        if m not in G2t[l]:
            break
    M = {x: l, y: m}
    def put(A, B):
        A, B = sorted(A), sorted(B); assert len(A) == len(B)
        rng.shuffle(B)
        for u, v in zip(A, B):
            assert u not in M; M[u] = v
    cs, ct = G2s[x] & G2s[y], G2t[l] & G2t[m]
    put(cs, ct); put(G2s[x] - cs, G2t[l] - ct); put(G2s[y] - cs, G2t[m] - ct)
    rest_s = [u for u in range(N) if u not in M]; rest_t = sorted(set(range(N)) - set(M.values()))
    put(rest_s, rest_t)
    for u in (x, y):                               # (H3)
        assert {M[a] for a in G2s[u]} == G2t[M[u]]
    return [M[u] for u in range(N)], [x, y]

def pg2(F):
    pts = proj_points(F, 3)
    idx = {p: i for i, p in enumerate(pts)}
    m, a = F.mul, F.add
    inc = [[i for i, p in enumerate(pts) if a[a[m[L[0]][p[0]]][m[L[1]][p[1]]]][m[L[2]][p[2]]] == 0] for L in pts]
    return len(pts), inc            # line j (dual coordinates pts[j]) -> its points

def hub_graph(spec, KB, KA, delta, rng):
    """Lemma 9.1; returns edges (b, a) with b < KB, a < KA. B = points/'B side', A = lines/'A side'."""
    parts = spec.split(':'); kind = parts[0]; s = int(parts[1])
    edges = []
    if kind in ('Y1', 'Y2'):
        if kind == 'Y1':
            nP, inc = pg2(GF(s)); nL = nP
            lines_with_pend = list(range(nL)); pts_with_pend = list(range(nP))
        else:
            Ws = W(GF(s)); nP = nL = Ws.N; inc = Ws.lp
            z0 = 0; m0 = 0
            lines_with_pend = list(Ws.pl[z0]); pts_with_pend = list(Ws.lp[m0])
        assert s + 1 <= delta and KB >= nP and KA >= nL
        for j in range(nL):
            for p in inc[j]:
                edges.append((p, j))
        cap = delta - s - 1
        assert KB - nP <= cap * len(lines_with_pend) and KA - nL <= cap * len(pts_with_pend)
        for k in range(KB - nP):          # pendant B-vertices on lines, round robin
            edges.append((nP + k, lines_with_pend[k % len(lines_with_pend)]))
        for k in range(KA - nL):          # pendant A-vertices on points
            edges.append((pts_with_pend[k % len(pts_with_pend)], nL + k))
    elif kind == 'Y3':
        rp = int(parts[2]); Ws = W(GF(s)); N = Ws.N; nlev = 2 * rp + 1
        assert s + 1 + rp <= delta and KB == KA == nlev * N
        for j in range(nlev):
            for l in range(N):
                for p in Ws.lp[l]:
                    edges.append((j * N + p, j * N + l))           # B = points, A = lines
        for j in range(nlev):
            for k in range(1, rp + 1):
                jj = (j + k) % nlev; perm = list(range(N)); rng.shuffle(perm)
                for p in range(N):
                    edges.append((j * N + p, jj * N + perm[p]))    # point of j -> line of jj (all H)
    else:
        raise ValueError(spec)
    dB = [0] * KB; dA = [0] * KA
    for b, a in edges:
        dB[b] += 1; dA[a] += 1
    assert max(dB) <= delta and max(dA) <= delta
    return edges

def build(cor, q, r, KB, KA, hubspec, seed=0, variant=None):
    rng = random.Random(seed)
    F = GF(q); Wq = W(F)
    if cor == '10.1':
        assert q % 2 == 0
        G = Wq; types = 'H' * (2 * r + 1)
        psi, phi = lemma14_duality(F, Wq)
        OW = [psi[l] for l in lemma11_spread(F, Wq)]               # ovoid of W(q)
        assert all(b not in Wq.collinear[a] for a, b in itertools.combinations(OW, 2))
    else:
        assert q % 2 == 1
        Qq = Q4(F); G = Qq
        lp, pl = klein(F, Wq, Qq)
        O = [lp[l] for l in lemma11_spread(F, Wq)]                  # ovoid of Q(4,q)
        assert all(b not in Qq.collinear[a] for a, b in itertools.combinations(O, 2))
        Tl = [pl[p] for p in lemma13_partial_ovoid(F, Wq, rng)]     # partial spread of Q(4,q)
        assert all(b not in Qq.meets[a] for a, b in itertools.combinations(Tl, 2))
        if variant == 'plus1':                                      # one more line meeting a line of the set
            extra = next(m for m in sorted(Qq.meets[Tl[0]]) if m not in Tl)
            Tl = Tl + [extra]
        types = {'10.2': 'HHDHD', '10.3': 'HHHDHHD', '10.4': 'HHHHDHHHD'}[cor]
        assert len(types) == 2 * r + 1
    N = G.N; nlev = 2 * r + 1
    arcs = [(j, (j + k) % nlev) for j in range(nlev) for k in range(1, r + 1)]
    A = {'H': 'P', 'D': 'L'}; B = {'H': 'L', 'D': 'P'}
    vid = lambda j, t, e: j * 2 * N + (e if t == 'P' else N + e)
    M = {}; R = {}
    for (j, k) in arcs:
        tj, tk = types[j], types[k]
        if cor == '10.1':
            M[(j, k)] = phi; R[(j, k)] = OW
        elif tj != tk:
            M[(j, k)] = list(range(N)); R[(j, k)] = O if tj == 'H' else Tl
        else:
            M[(j, k)], R[(j, k)] = local_duality(G, A[tj], rng)
    edges = []
    for j in range(nlev):
        for l in range(N):
            for p in G.lp[l]:
                edges.append((vid(j, 'P', p), vid(j, 'L', l)))
    freeA = [[] for _ in range(nlev)]; freeB = [[] for _ in range(nlev)]
    for (j, k) in arcs:
        Rs = set(R[(j, k)])
        for a in range(N):
            if a in Rs:
                freeA[j].append(vid(j, A[types[j]], a)); freeB[k].append(vid(k, B[types[k]], M[(j, k)][a]))
            else:
                edges.append((vid(j, A[types[j]], a), vid(k, B[types[k]], M[(j, k)][a])))
    alpha = [len(x) for x in freeA]; beta = [len(x) for x in freeB]
    assert KB <= min(alpha) and KA <= min(beta), (alpha, beta)
    base = nlev * 2 * N
    for j in range(nlev):                       # any slot assignment (Theorem 3.5 puts no condition on it)
        sa = rng.sample(freeA[j], KB); sb = rng.sample(freeB[j], KA)
        for h in range(KB):
            edges.append((base + h, sa[h]))
        for g in range(KA):
            edges.append((base + KB + g, sb[g]))
    for (b, a) in hub_graph(hubspec, KB, KA, q - r, rng):
        edges.append((base + b, base + KB + a))
    n = base + KB + KA
    return n, edges, alpha, beta

if __name__ == '__main__':
    cor, q, r, KB, KA, hub, out = sys.argv[1:8]
    seed = int(sys.argv[8]) if len(sys.argv) > 8 else 0
    variant = sys.argv[9] if len(sys.argv) > 9 else None
    n, edges, alpha, beta = build(cor, int(q), int(r), int(KB), int(KA), hub, seed, variant)
    print("Cor %s q=%s r=%s alpha=%s beta=%s KB=%s KA=%s hubs=%s: n=%d" % (cor, q, r, alpha, beta, KB, KA, hub, n))
    with open(out, 'w') as f:
        f.write("%d\n" % n)
        f.writelines("%d %d\n" % e for e in edges)
