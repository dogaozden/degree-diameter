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
TIME_FRAC = 0.8               # fraction of time_limit used for search
POST_FRAC = 0.85              # fraction of time_limit after which nothing new starts
POST_EXTEND_SLICE = 1.5       # seconds given to greedy extension of the best lift
C_MOORE_MAX = 512             # the D=3 C engine supports at most 512 vertices


# ---------------------------------------------------------------- C engine (D = 3 growth search)

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 512
#define DMAX 32
#define WMAX 8
#define EMAX (NMAX * DMAX)
#define STALL 400000ULL
#define TPER 200000ULL
#define TH 2.0
#define TL 0.05

static int D_DEG;
static int nmax;
static int n;
static int nedges;
static int nb[NMAX][DMAX];
static int deg[NMAX];
static unsigned char M[NMAX][NMAX];
static int col[NMAX];
static int side[2][NMAX];
static int sideN[2];
static uint64_t B1[NMAX][WMAX], B2[NMAX][WMAX];
static int bestN, bestM;
static int bestE[EMAX][2];
static uint64_t rs = 88172645463325252ULL;
static clock_t T0;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
#if defined(__GNUC__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static void rem_nb(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (nb[u][k] == v) { nb[u][k] = nb[u][--deg[u]]; return; }
}

static void addE(int u, int v) {
    M[u][v] = 1; M[v][u] = 1;
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    nedges++;
}

static void delE(int u, int v) {
    M[u][v] = 0; M[v][u] = 0;
    rem_nb(u, v);
    rem_nb(v, u);
    nedges--;
}

/* Number of unordered vertex pairs at distance > 3 (zero iff valid). */
static long cost(void) {
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B1[v][w] = 0;
        B1[v][v >> 6] |= 1ULL << (v & 63);
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            B1[v][u >> 6] |= 1ULL << (u & 63);
        }
    }
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B2[v][w] = B1[v][w];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            for (int w = 0; w < W; w++) B2[v][w] |= B1[u][w];
        }
    }
    long bad2 = 0;
    for (int v = 0; v < n; v++) {
        uint64_t acc[WMAX];
        for (int w = 0; w < W; w++) acc[w] = B2[v][w];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            for (int w = 0; w < W; w++) acc[w] |= B2[u][w];
        }
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += popc(acc[w]);
        bad2 += n - cnt;
    }
    return bad2 / 2;
}

static int pick(int c) {
    if (sideN[c] == 0) return -1;
    for (int t = 0; t < 30; t++) {
        int v = side[c][rndint(sideN[c])];
        if (deg[v] > 0) return v;
    }
    return -1;
}

static int pick_def(int c, int avoid) {
    if (sideN[c] == 0) return -1;
    for (int t = 0; t < 30; t++) {
        int v = side[c][rndint(sideN[c])];
        if (deg[v] < D_DEG && v != avoid) return v;
    }
    return -1;
}

static int accept(long delta, double T) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / T);
}

static double temp_at(uint64_t it) {
    double ph = (double)(it % TPER) / (double)TPER;
    return TH * pow(TL / TH, ph);
}

static void save_best(void) {
    bestN = n;
    bestM = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (nb[u][k] > u) {
                bestE[bestM][0] = u;
                bestE[bestM][1] = nb[u][k];
                bestM++;
            }
}

static void load_best(void) {
    for (int i = 0; i < n; i++) {
        memset(M[i], 0, sizeof M[i]);
        deg[i] = 0;
    }
    n = bestN;
    nedges = 0;
    sideN[0] = 0;
    sideN[1] = 0;
    for (int v = 0; v < n; v++) side[col[v]][sideN[col[v]]++] = v;
    for (int e = 0; e < bestM; e++) addE(bestE[e][0], bestE[e][1]);
}

/* Add one new vertex on each side (isolated). */
static void grow_pair(void) {
    int a = n, b = n + 1;
    for (int x = 0; x < n; x++) { M[x][a] = 0; M[x][b] = 0; }
    memset(M[a], 0, sizeof M[a]);
    memset(M[b], 0, sizeof M[b]);
    deg[a] = 0;
    deg[b] = 0;
    col[a] = 0;
    col[b] = 1;
    side[0][sideN[0]++] = a;
    side[1][sideN[1]++] = b;
    n += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    T0 = clock();
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { printf("0 0\n"); return 0; }
    if (n0 <= 0 || n0 > NMAX || d < 2 || d > DMAX || D != 3 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    long long mb = 2LL * (1 + (d - 1) + (long long)(d - 1) * (d - 1));
    nmax = (mb < NMAX) ? (int)mb : NMAX;
    if (n0 > nmax) { printf("0 0\n"); return 0; }
    D_DEG = d;
    n = n0;
    nedges = 0;
    memset(M, 0, sizeof M);
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || M[u][v] || deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        addE(u, v);
    }

    /* 2-colour the input (any proper colouring works; new vertices get fixed colours). */
    for (int i = 0; i < n; i++) col[i] = -1;
    static int queue[NMAX];
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    sideN[0] = 0;
    sideN[1] = 0;
    for (int v = 0; v < n; v++) side[col[v]][sideN[col[v]]++] = v;

    bestN = 0;
    bestM = 0;
    long cur = cost();
    uint64_t it = 0, lastSucc = 0;

    while (1) {
        if (cur == 0) {
            if (n > bestN) save_best();
            if (n + 2 > nmax) break;
            grow_pair();
            cur = cost();
            lastSucc = it;
        }
        it++;
        if ((it & 255ULL) == 0 && elapsed() > tl) break;

        if (it - lastSucc > STALL && bestN > 0) {
            load_best();
            cur = cost();
            lastSucc = it;
            continue;
        }

        double T = temp_at(it);
        int r = rndint(100);

        if (r < 20) {
            /* Add an edge between two deficient vertices (never increases cost). */
            int a = pick_def(0, -1);
            int b = pick_def(1, -1);
            if (a >= 0 && b >= 0 && !M[a][b]) {
                addE(a, b);
                cur = cost();
            }
            continue;
        }

        if (r < 60) {
            /* Degree-preserving 2-switch across the bipartition. */
            int a1 = pick(0), a2 = pick(0);
            if (a1 < 0 || a2 < 0 || a1 == a2) continue;
            int b1 = nb[a1][rndint(deg[a1])];
            int b2 = nb[a2][rndint(deg[a2])];
            if (b1 == b2 || M[a1][b2] || M[a2][b1]) continue;
            delE(a1, b1);
            delE(a2, b2);
            addE(a1, b2);
            addE(a2, b1);
            long nc = cost();
            if (accept(nc - cur, T)) {
                cur = nc;
            } else {
                delE(a1, b2);
                delE(a2, b1);
                addE(a1, b1);
                addE(a2, b2);
            }
            continue;
        }

        /* Transfer: move one endpoint of an edge onto a deficient vertex. */
        {
            int a = pick(0);
            if (a < 0) continue;
            int b = nb[a][rndint(deg[a])];
            if (rndint(2)) {
                int x = pick_def(0, a);
                if (x < 0 || M[x][b]) continue;
                delE(a, b);
                addE(x, b);
                long nc = cost();
                if (accept(nc - cur, T)) {
                    cur = nc;
                } else {
                    delE(x, b);
                    addE(a, b);
                }
            } else {
                int y = pick_def(1, b);
                if (y < 0 || M[a][y]) continue;
                delE(a, b);
                addE(a, y);
                long nc = cost();
                if (accept(nc - cur, T)) {
                    cur = nc;
                } else {
                    delE(a, y);
                    addE(a, b);
                }
            }
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestE[e][0], bestE[e][1]);
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


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- D = 3 : new search path

def _build_d3(d, seed, time_limit):
    """Start from the best known D = 3 graph and let the C engine grow it.

    Start graph: Araujo-Pardo-Lopez graph for q = d-2 (record), else PG(2,q) incidence.
    The C engine repeatedly adds one vertex per side and anneals (edge switches and
    endpoint transfers) until the diameter is restored. Every output is re-checked.
    """
    start = time.monotonic()
    pg = _pg_base(d)
    if pg is None:
        pg = lib.haar_graph(d, range(d))
    if lib.is_prime_power(d - 1):
        return _finish([pg], d, 3)  # Moore-extremal, nothing to improve

    base = pg
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            al = lib.araujo_lopez_graph(q)
            if al[0] > pg[0] and lib.is_valid(al[0], al[1], d, 3):
                base = al
        except ValueError:
            pass

    best = _finish([pg, base], d, 3)
    if not lib.is_valid(base[0], base[1], d, 3):
        return best
    if base[0] > C_MOORE_MAX or lib._moore_bound(d, 3) > C_MOORE_MAX:
        return best

    elapsed = time.monotonic() - start
    budget = 0.8 * time_limit - 2.5 - elapsed
    if budget < 1.0:
        return best
    timeout = max(1.0, 0.95 * time_limit - elapsed)
    try:
        text = lib.run_c(C_SOURCE, [d, 3, seed, round(budget, 2)],
                         stdin_graph=base, timeout=timeout)
        n, e = lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return best
    if n > best[0] and lib.is_valid(n, e, d, 3):
        best = (n, e)
    return best


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


# ---------------------------------------------------------------- legacy driver (other cases)

def _legacy_build(d, D, seed, time_limit):
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
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

    # D >= 4: generalized quadrangle W(q) (diameter 4 <= D), extended as well.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            if D == 4 and d - 1 <= GQ_Q_MAX and lib.is_prime_power(d - 1):
                return _finish(cands + [gq], d, D)  # Moore-extremal for D = 4
            cands.append(gq)
            aug = _augment(gq[0], gq[1], d, seed)
            for g in (gq, aug):
                cands.append(_extend(g[0], g[1], d, D, rng, min(deadline, time.monotonic() + 0.7)))

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

    return _finish(cands, d, D)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    if D == 3 and 3 <= d <= 16:
        return _build_d3(d, seed, time_limit)
    return _legacy_build(d, D, seed, time_limit)
