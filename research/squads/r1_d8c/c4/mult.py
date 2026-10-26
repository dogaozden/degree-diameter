"""c4: multiplicative coordinate voltages on I(H(q)) (prime q), diversity measurement and Z_{5d} lifts.

Flag (p, L): p = alpha*e_L + beta*f_L (e_L = first point, f_L = second point of L in LP order);
r = alpha/beta in GF(q)* u {0, inf}; w(p,L) = dlog_g(r) in Z_{q-1} (special points e_L, f_L get value SPEC),
reduced mod d (d | q-1).
"""
import sys, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/cells/d10D8_work')
from hexlib import load

HERE = '/home/user/degree-diameter/research/squads/r1_d8c/c4'
PRIM = {5: 2, 7: 3, 3: 2, 11: 2, 13: 2}


def dlog_table(q):
    g = PRIM[q]
    t = {}
    x = 1
    for k in range(q - 1):
        t[x] = k
        x = x * g % q
    return t


def mult_voltages(q, N, LP, coord, spec=0):
    """returns W[L, k] = dlog ratio in Z_{q-1} for flag (LP[L,k], L); special for k=0 (e) and k=1 (f)."""
    lg = dlog_table(q)
    W = np.zeros(LP.shape, dtype=np.int64)
    bad = 0
    for L in range(LP.shape[0]):
        e = coord[LP[L, 0]].astype(np.int64)
        f = coord[LP[L, 1]].astype(np.int64)
        # choose coordinates i,k with nonzero 2x2 determinant
        found = None
        for i in range(7):
            for k in range(7):
                det = (e[i] * f[k] - e[k] * f[i]) % q
                if det:
                    found = (i, k, pow(int(det), q - 2, q))
                    break
            if found:
                break
        i, k, dinv = found
        for j in range(q + 1):
            p = coord[LP[L, j]].astype(np.int64)
            # solve alpha e + beta f = p using rows i,k: [e_i f_i; e_k f_k][alpha; beta] = [p_i; p_k]
            alpha = ((p[i] * f[k] - f[i] * p[k]) * dinv) % q
            beta = ((e[i] * p[k] - e[k] * p[i]) * dinv) % q
            if not (((alpha * e + beta * f - p) % q) == 0).all():
                bad += 1
            if j == 0:
                W[L, j] = spec
            elif j == 1:
                W[L, j] = spec
            else:
                # alpha, beta nonzero for j>=2 (p != e, f)
                W[L, j] = lg[int(alpha * pow(int(beta), q - 2, q) % q)]
    assert bad == 0, bad
    return W


def geodesics(q, N, LP, PL, src, dst, adj):
    """all shortest paths src->dst in incidence graph; vertices: points 0..N-1, lines N..2N-1.
    adj: list of neighbour lists. returns list of paths (lists of vertices)."""
    from collections import deque
    dist = {dst: 0}
    dq = deque([dst])
    while dq:
        u = dq.popleft()
        for v in adj[u]:
            if v not in dist:
                dist[v] = dist[u] + 1
                dq.append(v)
    D = dist[src]
    paths = []
    stack = [[src]]
    while stack:
        pth = stack.pop()
        u = pth[-1]
        if u == dst:
            paths.append(pth)
            continue
        for v in adj[u]:
            if dist.get(v, 999) == dist[u] - 1:
                stack.append(pth + [v])
    return D, paths


def build_adj(N, LP, PL):
    adj = [None] * (2 * N)
    for p in range(N):
        adj[p] = [N + int(l) for l in PL[p]]
    for l in range(N):
        adj[N + l] = [int(p) for p in LP[l]]
    return adj


def signed_sum(path, N, Wd, d, flagvol):
    s = 0
    for a, b in zip(path[:-1], path[1:]):
        if a < N:  # point -> line
            s += flagvol(a, b - N)
        else:      # line -> point
            s -= flagvol(b, a - N)
    return s % d


def measure(q, d, Wd, LP, PL, N, adj, trials=200, rng=random.Random(1), label=''):
    """distinct geodesic voltage sums (mod d) across the q+1 geodesics, for opposite point pairs and opposite line pairs."""
    pos = {}
    for l in range(N):
        for k, p in enumerate(LP[l]):
            pos[(int(p), l)] = k
    def fv(p, l):
        return Wd[l, pos[(p, l)]]
    res = {'pts': [], 'lines': []}
    for kind in ('pts', 'lines'):
        for _ in range(trials):
            if kind == 'pts':
                x = rng.randrange(N)
                # opposite point: distance 6 -> vertex N + something; sample until a point at distance 6
            else:
                x = N + rng.randrange(N)
            # BFS from x
            from collections import deque
            dist = {x: 0}; dq = deque([x])
            while dq:
                u = dq.popleft()
                for v in adj[u]:
                    if v not in dist:
                        dist[v] = dist[u] + 1; dq.append(v)
            far = [v for v in dist if dist[v] == 6 and ((v < N) == (x < N))]
            if not far:
                continue
            y = rng.choice(far)
            D, paths = geodesics(q, N, LP, PL, x, y, adj)
            assert D == 6 and len(paths) == q + 1, (D, len(paths))
            sums = {signed_sum(p, N, Wd, d, fv) for p in paths}
            res[kind].append(len(sums))
    return {k: (float(np.mean(v)), len(v)) for k, v in res.items()}


def write_lift(fn, N, m, flags, matchings):
    """flags: (N_flags,3) (point, line, voltage in Z_m); matchings: list of (perm array, voltage)."""
    E = [tuple(x) for x in flags]
    for perm, v in matchings:
        for p in range(N):
            E.append((p, int(perm[p]), v))
    with open(fn, 'w') as f:
        f.write(f'{N} {N} {m}\n')
        for a, b, v in E:
            f.write(f'{a} {b} {v % m}\n')
    return len(E)


def crt(a5, bd, d, m=None):
    """element of Z_{5d} with x = a5 mod 5, x = bd mod d (gcd(5,d)=1)."""
    for x in range(5 * d):
        if x % 5 == a5 % 5 and x % d == bd % d:
            return x
    raise ValueError
