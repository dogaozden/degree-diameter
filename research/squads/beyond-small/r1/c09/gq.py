# W(q) = symplectic generalized quadrangle of order (q,q), q in {7,8,9}; incidence graph + polarity search (q=8).
# Vertices of the incidence graph: 0..N-1 points, N..2N-1 lines.
import sys, random, itertools

def field(q):
    if q == 7:
        p, e, mod = 7, 1, None
    elif q == 8:
        p, e, mod = 2, 3, [1, 1, 0]          # x^3 + x + 1 (coeffs low->high, monic x^3 implicit)
    elif q == 9:
        p, e, mod = 3, 2, [1, 0]             # x^2 + 1
    else:
        raise ValueError(q)
    def tovec(a):
        v = []
        for _ in range(e):
            v.append(a % p); a //= p
        return v
    def toint(v):
        s = 0
        for c in reversed(v): s = s * p + c
        return s
    ADD = [[0] * q for _ in range(q)]
    MUL = [[0] * q for _ in range(q)]
    for a in range(q):
        va = tovec(a)
        for b in range(q):
            vb = tovec(b)
            ADD[a][b] = toint([(x + y) % p for x, y in zip(va, vb)])
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e):
                    r[i + j] = (r[i + j] + va[i] * vb[j]) % p
            if e > 1:
                for k in range(2 * e - 2, e - 1, -1):
                    f = r[k]
                    if f:
                        r[k] = 0
                        # x^e = -(mod coeffs): x^e = -sum mod[i] x^i  (mod list is for x^e monic)
                        for i in range(e):
                            r[k - e + i] = (r[k - e + i] - f * mod[i]) % p
            MUL[a][b] = toint(r[:e])
    NEG = [next(b for b in range(q) if ADD[a][b] == 0) for a in range(q)]
    INV = [0] * q
    for a in range(1, q):
        INV[a] = next(b for b in range(q) if MUL[a][b] == 1)
    return ADD, MUL, NEG, INV

def build(q):
    ADD, MUL, NEG, INV = field(q)
    def norm(v):
        for i in range(4):
            if v[i]:
                s = INV[v[i]]
                return tuple(MUL[s][x] for x in v)
        return None
    pts = []
    seen = set()
    for v in itertools.product(range(q), repeat=4):
        n = norm(v)
        if n is not None and n == v:
            pts.append(v)
    idx = {v: i for i, v in enumerate(pts)}
    N = len(pts)
    assert N == (q + 1) * (q * q + 1), N
    def B(x, y):  # x0y1 - x1y0 + x2y3 - x3y2
        t1 = MUL[x[0]][y[1]]; t2 = MUL[x[1]][y[0]]; t3 = MUL[x[2]][y[3]]; t4 = MUL[x[3]][y[2]]
        s = ADD[ADD[t1][NEG[t2]]][ADD[t3][NEG[t4]]]
        return s
    def comb(a, x, b, y):
        return tuple(ADD[MUL[a][u]][MUL[b][w]] for u, w in zip(x, y))
    lines = {}
    for i, x in enumerate(pts):
        for j, y in enumerate(pts):
            if i == j or B(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    n = norm(comb(a, x, b, y))
                    if n is not None:
                        L.add(idx[n])
            key = frozenset(L)
            if key not in lines:
                lines[key] = len(lines)
    linelist = sorted(lines.keys(), key=lambda s: sorted(s))
    assert len(linelist) == N, len(linelist)
    nbr = [0] * (2 * N)   # bitmask adjacency
    pl = [[] for _ in range(N)]
    lp = []
    for li, L in enumerate(linelist):
        lp.append(sorted(L))
        for p in L:
            nbr[p] |= 1 << (N + li)
            nbr[N + li] |= 1 << p
            pl[p].append(li)
    return dict(q=q, N=N, pts=pts, nbr=nbr, lp=lp, pl=pl)

def adjlist(G):
    N = G['N']
    out = []
    for v in range(2 * N):
        m = G['nbr'][v]; out.append([u for u in range(2 * N) if m >> u & 1])
    return out

def find_polarity(G, seed=1, limit_nodes=2000000):
    """Backtracking for an involutive side-swapping automorphism of the incidence graph (a polarity)."""
    sys.setrecursionlimit(10000)
    N = G['N']; nbr = G['nbr']; V = 2 * N
    full_pts = (1 << N) - 1
    side_mask = [((full_pts << N) if v < N else full_pts) for v in range(V)]
    rng = random.Random(seed)
    phi = [-1] * V
    nodes = [0]
    def assign(dom, v, w):
        # phi(v)=w and phi(w)=v; returns new dom or None
        d = dom[:]
        for (a, b) in ((v, w), (w, v)):
            if not (d[a] >> b & 1):
                return None
        for (a, b) in ((v, w), (w, v)):
            phi[a] = b
        bits_clear = ~((1 << v) | (1 << w))
        for x in range(V):
            if phi[x] >= 0:
                continue
            dx = d[x] & bits_clear
            # constraint from phi(v)=w and phi(w)=v
            for a in (v, w):
                b = phi[a]
                if nbr[a] >> x & 1:
                    dx &= nbr[b]
                else:
                    dx &= ~nbr[b]
            d[x] = dx
            if dx == 0:
                for a in (v, w): phi[a] = -1
                return None
        d[v] = 0; d[w] = 0
        return d
    def undo(v, w):
        phi[v] = -1; phi[w] = -1
    def rec(dom):
        nodes[0] += 1
        if nodes[0] > limit_nodes:
            raise RuntimeError('node limit')
        best = None; bc = 10 ** 9
        for x in range(V):
            if phi[x] < 0:
                c = dom[x].bit_count()
                if c == 0:
                    return False
                if c < bc:
                    bc = c; best = x
                    if c == 1:
                        break
        if best is None:
            return True
        x = best
        cand = [b for b in range(V) if dom[x] >> b & 1]
        rng.shuffle(cand)
        for w in cand:
            nd = assign(dom, x, w)
            if nd is None:
                continue
            if rec(nd):
                return True
            undo(x, w)
        return False
    dom0 = [side_mask[v] for v in range(V)]
    ok = rec(dom0)
    return phi[:] if ok else None

def check_auto(G, phi):
    V = 2 * G['N']; nbr = G['nbr']; N = G['N']
    assert sorted(phi) == list(range(V))
    for v in range(V):
        w = phi[v]
        assert (v < N) != (w < N)
        for u in range(V):
            if (nbr[v] >> u & 1) != (nbr[w] >> phi[u] & 1):
                return False
    return all(phi[phi[v]] == v for v in range(V))

if __name__ == '__main__':
    q = int(sys.argv[1])
    G = build(q)
    print('q', q, 'N', G['N'], flush=True)
    if len(sys.argv) > 2 and sys.argv[2] == 'polarity':
        import time
        t = time.time()
        for seed in range(1, 50):
            try:
                phi = find_polarity(G, seed=seed, limit_nodes=20000)
            except RuntimeError:
                print('seed', seed, 'node limit', flush=True); continue
            if phi is not None:
                print('found seed', seed, 'valid', check_auto(G, phi), 'time', round(time.time() - t, 1), flush=True)
                with open(f'/home/user/degree-diameter/research/squads/beyond-small/r1/c09/polarity_q{q}.txt', 'w') as f:
                    f.write(' '.join(map(str, phi)) + '\n')
                break
            print('seed', seed, 'no polarity', flush=True)
