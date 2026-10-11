import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count
ITERS = 6000                  # annealing iterations per attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
GQ_Q_MAX = 9                  # largest q for which W(q) is built (pair loop is O(P^2))
RETRIES = 2                   # annealing attempts per candidate lift size
TIME_FRAC = 0.5               # fraction of time_limit used for Python search
POST_FRAC = 0.55              # fraction of time_limit after which nothing new starts in Python
POST_EXTEND_SLICE = 1.5       # seconds given to greedy extension of the best lift
C_FRAC = 0.9                  # fraction of time_limit by which the C growth must finish


# ---------------------------------------------------------------- C growth engine

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4000
#define MAXDEG 64
#define MAXD 200

static int n, D, DEG, INFV;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int col[MAXN];
static unsigned char dist[MAXN][MAXN];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void two_colour(void) {
    static int st[MAXN];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (col[w] == -1) { col[w] = 1 - col[u]; st[sp++] = w; }
            }
        }
    }
}

static void bfs_all(void) {
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        unsigned char *ds = dist[s];
        for (int v = 0; v < n; v++) ds[v] = (unsigned char)INFV;
        ds[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            int du = ds[u];
            if (du >= D) continue;
            for (int i = 0; i < deg[u]; i++) {
                int w = adj[u][i];
                if (ds[w] == INFV) { ds[w] = (unsigned char)(du + 1); q[t++] = w; }
            }
        }
    }
}

/* Add a new vertex of colour c adjacent to S[0..k-1]; keeps dist exact (capped at INFV). */
static void add_vertex(int c, const int *S, int k) {
    int x = n;
    static int dx[MAXN];
    for (int v = 0; v < x; v++) {
        int best = INFV;
        for (int i = 0; i < k; i++) {
            int dd = dist[S[i]][v];
            if (dd < best) best = dd;
        }
        int val = best + 1;
        dx[v] = (val > D) ? INFV : val;
    }
    n++;
    col[x] = c;
    deg[x] = 0;
    for (int i = 0; i < k; i++) {
        int u = S[i];
        adj[u][deg[u]++] = x;
        adj[x][deg[x]++] = u;
    }
    dx[x] = 0;
    for (int a = 0; a < x; a++) {
        dist[a][x] = (unsigned char)dx[a];
        dist[x][a] = (unsigned char)dx[a];
    }
    dist[x][x] = 0;
    for (int a = 0; a < x; a++) {
        int da = dx[a];
        if (da >= INFV) continue;
        for (int b = 0; b < x; b++) {
            int s = da + dx[b];
            if (s < dist[a][b]) dist[a][b] = (unsigned char)s;
        }
    }
}

/* Add edge u-v (u, v of opposite colours with spare degree); updates dist exactly. */
static void add_edge(int u, int v) {
    static int du[MAXN], dv[MAXN];
    for (int a = 0; a < n; a++) { du[a] = dist[a][u]; dv[a] = dist[a][v]; }
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    for (int a = 0; a < n; a++) {
        for (int b = 0; b < n; b++) {
            int s1 = du[a] + 1 + dv[b];
            int s2 = dv[a] + 1 + du[b];
            int s = s1 < s2 ? s1 : s2;
            if (s < dist[a][b]) dist[a][b] = (unsigned char)s;
        }
    }
}

/* Randomised greedy set cover: find neighbours S (other colour, spare degree) whose
   radius-(D-1) balls cover all vertices; then add a new vertex adjacent to S. */
static int try_extend(void) {
    static int cand[MAXN];
    static unsigned char covered[MAXN];
    int c = rndi(2);
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - c && deg[u] < DEG) cand[nc++] = u;
    if (nc == 0) return 0;
    memset(covered, 0, (size_t)n);
    int uncovered = n;
    int S[MAXDEG];
    int k = 0;
    int lim = D - 1;
    while (uncovered > 0 && k < DEG) {
        int besti = -1;
        double bests = -1.0;
        for (int i = 0; i < nc; i++) {
            if (cand[i] < 0) continue;
            const unsigned char *row = dist[cand[i]];
            int g = 0;
            for (int v = 0; v < n; v++)
                if (!covered[v] && row[v] <= lim) g++;
            if (g == 0) continue;
            double sc = g + 1.5 * rndd();
            if (sc > bests) { bests = sc; besti = i; }
        }
        if (besti < 0) break;
        int u = cand[besti];
        cand[besti] = -1;
        S[k++] = u;
        const unsigned char *row = dist[u];
        for (int v = 0; v < n; v++)
            if (!covered[v] && row[v] <= lim) { covered[v] = 1; uncovered--; }
    }
    if (uncovered > 0 || k == 0) return 0;
    add_vertex(c, S, k);
    return 1;
}

/* Add a random edge between spare-degree vertices of opposite colours. */
static int try_spare_edge(void) {
    for (int tries = 0; tries < 400; tries++) {
        int u = rndi(n), v = rndi(n);
        if (col[u] == col[v] || deg[u] >= DEG || deg[v] >= DEG) continue;
        int dup = 0;
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] == v) { dup = 1; break; }
        if (dup) continue;
        add_edge(u, v);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    double tl = atof(argv[4]);
    DEG = d;
    INFV = D + 1;
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (!rs) rs = 1;

    int n_in, m_in;
    if (scanf("%d %d", &n_in, &m_in) != 2) { printf("0 0\n"); return 0; }
    if (n_in < 1 || n_in >= MAXN - 1 || D < 2 || D > MAXD || d < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    n = n_in;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    clock_t t0 = clock();
    double limit = tl * (double)CLOCKS_PER_SEC;
    two_colour();
    bfs_all();

    int fails = 0;
    while ((double)(clock() - t0) < limit && n + 1 < MAXN) {
        if (try_extend()) { fails = 0; continue; }
        if (try_spare_edge()) continue;
        if (++fails > 3000) break;
    }

    long long msum = 0;
    for (int u = 0; u < n; u++) msum += deg[u];
    printf("%d %lld\n", n, msum / 2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++) {
            int w = adj[u][i];
            if (u < w) printf("%d %d\n", u, w);
        }
    return 0;
}
"""


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


def _best_valid(cands, d, D):
    """Return the largest valid candidate, or None."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return None


def _c_grow(start, d, D, seed, budget, timeout):
    """Run the C engine from a valid start graph; return (n, edges) or None on any failure."""
    n, edges = start
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=timeout)
        gn, ge = lib.parse_graph_text(out)
    except Exception:
        return None
    if gn <= 0:
        return None
    return gn, ge


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D >= 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q <= d-1 and q <= GQ_Q_MAX."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- Haar graphs (hill-climb)

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


# ---------------------------------------------------------------- lifts (annealing)

def _neighbors(P, Pinv, V, s, m):
    """Neighbour table (n x d) of the Z_m lift of a d-regular bipartite base on s+s vertices."""
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal(s, m, d, D, rng, deadline):
    """Simulated annealing over permutations and voltages. Returns (P, V) with zero cost, or None."""
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
    """Materialise the lift as (n, edges), deduplicated."""
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _try_size(s, m, d, D, rng, deadline):
    """Attempt to anneal a valid lift of size m, with a few independent restarts."""
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest m (doubling then bisection) whose lift passes annealing."""
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try_size(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - 1.0)
    post_end = start + max(0.5, POST_FRAC * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # D >= 3: projective plane (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1) and D == 3:   # Moore-extremal, nothing to improve
                return _finish(cands + [base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            for g in (base, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.5)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.5)))

    cap = min(N_CAP, lib._moore_bound(d, D))

    # Haar graphs with growing modulus (small slice of the remaining time).
    now = time.monotonic()
    haar_frac = 0.2 if D <= 4 else 0.1
    haar_end = now + haar_frac * max(0.0, deadline - now)
    haar_best, haar_m, haar_miss = None, d + 1, 0
    while time.monotonic() < haar_end and haar_miss < 4:
        S = _search_haar(d, D, haar_m, rng, haar_end, 120)
        if S is not None:
            haar_best = lib.haar_graph(haar_m, S)
            haar_miss = 0
        else:
            haar_miss += 1
        haar_m += 1
    if haar_best is not None:
        cands.append(haar_best)

    # Voltage-lift annealing, one slice per base size s.
    lift_best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            g = _graph(s, m, P, V, d)
            cands.append(g)
            if lift_best is None or g[0] > lift_best[0]:
                lift_best = g

    # Post-process the largest lift: fill spare degree by augmentation, then extend.
    if lift_best is not None and time.monotonic() < post_end:
        aug = _augment(lift_best[0], lift_best[1], d, seed)
        cands.append(aug)
        ext_end = min(post_end, time.monotonic() + POST_EXTEND_SLICE)
        cands.append(_extend(aug[0], aug[1], d, D, rng, ext_end))

    # C growth: start from the largest valid candidate and add vertices greedily
    # with randomised set-cover restarts, using the remaining time.
    base_best = _best_valid(cands, d, D)
    if base_best is not None and D >= 3 and d >= 3:
        now = time.monotonic()
        c_end = start + max(0.5, C_FRAC * time_limit - 1.0)
        budget = c_end - now
        if budget > 0.5:
            hard_end = start + 0.93 * time_limit
            timeout = max(1.0, hard_end - now)
            grown = _c_grow(base_best, d, D, seed, budget, timeout)
            if grown is not None:
                cands.append(grown)

    return _finish(cands, d, D)
