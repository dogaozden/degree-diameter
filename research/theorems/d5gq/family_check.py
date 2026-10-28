"""Independent end-to-end check of Corollaries 10.2/10.3 (and a nine-level analogue) with explicit ingredients:
ovoid of Lemma 1.1, partial ovoid of Lemma 1.3, two-point local dualities (Prop 6.4, random pieces),
hub graph PG(2,s)+pendants (Lemma 9.1 (Y1)), arbitrary hub slot assignment (Theorem 3.5)."""
import sys, random, itertools, subprocess, numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/chartlift')
from gqlib import W, regular_spread_W, is_partial_ovoid, is_partial_spread, _norm
from gf import GF
APSP = '/home/user/degree-diameter/research/theorems/d5gq/apsp'

def lemma13(Wq, q):
    F = Wq.F; A, M, S_ = F.add, F.mul, F.sub
    perp = lambda v: (F.neg[v[1]], v[0])
    a = [(1, 0), (0, 1), (1, 1)]; b = [perp(a[(i - 1) % 3]) for i in range(3)]
    pts = [(a[i][0], a[i][1], M[c][b[i][0]], M[c][b[i][1]]) for i in range(3) for c in range(1, q)]
    tau = 2; x = (1, tau)
    prop = lambda u, v: S_[M[u[0]][v[1]]][M[u[1]][v[0]]] == 0
    z = next(z for z in [(1, t) for t in range(q)] + [(0, 1)] if not any(prop(z, y) for y in a + [x]))
    zp = perp(z)
    pts += [(x[0], x[1], 0, 0), (0, 0, zp[0], zp[1])]
    return sorted(Wq.index[_norm(F, p)] for p in pts)

def local_duality(H, rng):
    """Prop 6.4 on H (points -> lines), random x,y,l,m and random piece bijections"""
    n = H.np
    while True:
        x, y = rng.sample(range(n), 2)
        if not H.col[x, y]: break
    while True:
        l, m = rng.sample(range(H.nl), 2)
        if not H.con[l, m]: break
    Mp = {x: l, y: m}
    cxy = list(np.nonzero(H.col[x] & H.col[y])[0]); clm = list(np.nonzero(H.con[l] & H.con[m])[0])
    rng.shuffle(clm); Mp.update(zip(cxy, clm))
    for u, w_ in ((x, l), (y, m)):
        A_ = [p for p in np.nonzero(H.col[u])[0] if p not in Mp]
        used = set(Mp.values())
        B_ = [k for k in np.nonzero(H.con[w_])[0] if k not in used]
        assert len(A_) == len(B_); rng.shuffle(B_); Mp.update(zip(A_, B_))
    used = set(Mp.values())
    ra = [p for p in range(n) if p not in Mp]; rb = [k for k in range(H.nl) if k not in used]
    rng.shuffle(rb); Mp.update(zip(ra, rb))
    M = [Mp[p] for p in range(n)]
    assert sorted(M) == list(range(H.nl))
    return M, {x, y}

def pg2(s):
    F = GF(s)
    pts = [v for v in itertools.product(range(s), repeat=3) if [c for c in v if c] and [c for c in v if c][0] == 1]
    inc = lambda p, l: F.add[F.add[F.mul[p[0]][l[0]]][F.mul[p[1]][l[1]]]][F.mul[p[2]][l[2]]] == 0
    return [(i, j) for i, p in enumerate(pts) for j, l in enumerate(pts) if inc(p, l)], len(pts)

def hubgraph_Y1(s, KB, KA, delta):
    E, v = pg2(s)
    assert v <= KB <= v * (delta - s) and v <= KA <= v * (delta - s)
    Y = [(p, l) for p, l in E]           # B-hub p (point), A-hub l (line)
    nb = v; na = v
    for i in range(KB - v):              # pendant B on line i % v
        Y.append((nb, i % v)); nb += 1
    for i in range(KA - v):              # pendant A on point i % v
        Y.append((i % v, na)); na += 1
    return Y

def build(q, types, KB, KA, s, seed=0):
    rng = random.Random(seed)
    L = len(types); r = (L - 1) // 2
    Wq = W(q); G = Wq.dual(); N = G.np
    O = regular_spread_W(Wq); assert is_partial_ovoid(G, O) and len(O) == q * q + 1
    S = lemma13(Wq, q) if q >= 5 else None
    assert len(S) == 3 * q - 1 and is_partial_ovoid(Wq, S) and is_partial_spread(G, S)
    per = 2 * N
    vid = lambda j, kind, i: j * per + (i if kind == 'P' else N + i)
    Ak = lambda t: 'P' if t == 'H' else 'L'
    Bk = lambda t: 'L' if t == 'H' else 'P'
    edges = []
    for j in range(L):
        for l, pts in enumerate(G.lines):
            for p in pts: edges.append((vid(j, 'P', p), vid(j, 'L', l)))
    Aslots = [[] for _ in range(L)]; Bslots = [[] for _ in range(L)]
    for j in range(L):
        for k in range(1, r + 1):
            j2 = (j + k) % L; tj, tj2 = types[j], types[j2]
            if tj == 'H' and tj2 == 'D': M = list(range(N)); R = set(O)
            elif tj == 'D' and tj2 == 'H': M = list(range(N)); R = set(S)
            elif tj == 'H': M, R = local_duality(G, rng)       # points of G -> lines of G
            else: M, R = local_duality(Wq, rng)                 # lines of G = points of W -> points of G = lines of W
            for a in range(N):
                u = vid(j, Ak(tj), a); v = vid(j2, Bk(tj2), M[a])
                if a in R: Aslots[j].append(u); Bslots[j2].append(v)
                else: edges.append((u, v))
    alpha = [len(x) for x in Aslots]; beta = [len(x) for x in Bslots]
    nv = L * per
    assert KB <= min(alpha) and KA <= min(beta), (alpha, beta)
    for x in Aslots + Bslots: rng.shuffle(x)
    for h in range(KB):
        for j in range(L): edges.append((nv + h, Aslots[j][h]))
    for g in range(KA):
        for j in range(L): edges.append((nv + KB + g, Bslots[j][g]))
    for (h, g) in hubgraph_Y1(s, KB, KA, q - r):
        edges.append((nv + h, nv + KB + g))
    n = nv + KB + KA
    path = 'fam_q%d_%s.edges' % (q, types)
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        for a, b in edges: f.write('%d %d\n' % (a, b))
    print(q, types, 'alpha', alpha, 'beta', beta, 'K_B', KB, 'K_A', KA, 'n', n, flush=True)
    print(subprocess.run([APSP, path, str(q + 1 + r), '5'], capture_output=True, text=True).stdout.strip(), flush=True)

if __name__ == '__main__':
    q = int(sys.argv[1]); types = sys.argv[2]; KB, KA, s = map(int, sys.argv[3:6])
    build(q, types, KB, KA, s, seed=int(sys.argv[6]) if len(sys.argv) > 6 else 0)
