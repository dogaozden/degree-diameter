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

MAX_GROW = 20                 # vertices the C engine may add beyond the start graph
C_TIME_FRAC = 0.75            # fraction of time_limit given to the C engine
C_TIMEOUT_FRAC = 0.92         # subprocess timeout as a fraction of time_limit


# ---------------------------------------------------------------- C engine
# Simulated annealing over bipartite graphs with max degree d and diameter <= 3.
# Moves: rewire an endpoint to a deficient vertex on the same side, add an edge
# between deficient vertices of opposite sides, or a degree-preserving 2-switch.
# Cost = number of unordered vertex pairs at distance > D. When cost hits 0 the
# state is saved and a new isolated vertex is added, so the search grows the graph.
# Only zero-cost states are ever emitted; otherwise the start graph is emitted.

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 1200
#define WCAP (NCAP / 64 + 2)
#define DCAP 30
#define ECAP 20000

#define T0 1.0
#define TMIN 0.2
#define TAU 20000.0

typedef uint64_t u64;

static int DIAM, DEG;
static int N;
static int side[NCAP];
static int deg[NCAP];
static int adj[NCAP][DCAP];
static u64 BA[NCAP][WCAP];
static u64 BB[NCAP][WCAP];
static int defA[NCAP], defB[NCAP];
static int seen_[NCAP], qbuf[NCAP];
static int sv_n, sv_m;
static int sv_u[ECAP], sv_v[ECAP];
static u64 rng_s = 88172645463325252ULL;

typedef struct { int type, a, b, c, d; } Move;

static u64 rnd64(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_half(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][--deg[u]];
            return;
        }
    }
}

static void remove_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long long cost_fn(void) {
    int w = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < w; j++) BA[v][j] = 0;
        BA[v][v >> 6] |= (u64)1 << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            for (int j = 0; j < w; j++) BB[v][j] = BA[v][j];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *src = BA[adj[v][k]];
                for (int j = 0; j < w; j++) BB[v][j] |= src[j];
            }
        }
        for (int v = 0; v < N; v++)
            for (int j = 0; j < w; j++) BA[v][j] = BB[v][j];
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int j = 0; j < w; j++) c += popc(BA[v][j]);
        bad += N - c;
    }
    return bad / 2;
}

static void apply_move(const Move *m) {
    switch (m->type) {
    case 1:  /* replace endpoint a by c on edge (a,b) */
        remove_edge(m->a, m->b);
        add_edge(m->c, m->b);
        break;
    case 2:  /* add edge (a,b) */
        add_edge(m->a, m->b);
        break;
    case 3:  /* 2-switch: (a,b),(c,d) -> (a,d),(c,b) */
        remove_edge(m->a, m->b);
        remove_edge(m->c, m->d);
        add_edge(m->a, m->d);
        add_edge(m->c, m->b);
        break;
    default:
        break;
    }
}

static void undo_move(const Move *m) {
    switch (m->type) {
    case 1:
        remove_edge(m->c, m->b);
        add_edge(m->a, m->b);
        break;
    case 2:
        remove_edge(m->a, m->b);
        break;
    case 3:
        remove_edge(m->a, m->d);
        remove_edge(m->c, m->b);
        add_edge(m->a, m->b);
        add_edge(m->c, m->d);
        break;
    default:
        break;
    }
}

static int propose_rewire(Move *m) {
    int a = rndint(N);
    if (!deg[a]) return 0;
    int q = adj[a][rndint(deg[a])];
    int p = a, o = q;
    if (rnd64() & 1) { p = q; o = a; }
    int s = side[p];
    int c = 0;
    for (int v = 0; v < N; v++)
        if (side[v] == s && v != p && deg[v] < DEG && !has_edge(v, o))
            defA[c++] = v;
    if (!c) return 0;
    int p2 = defA[rndint(c)];
    m->type = 1; m->a = p; m->b = o; m->c = p2; m->d = 0;
    apply_move(m);
    return 1;
}

static int propose_add(Move *m) {
    int ca = 0, cb = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (side[v] == 0) defA[ca++] = v;
            else defB[cb++] = v;
        }
    }
    if (!ca || !cb) return 0;
    for (int t = 0; t < 8; t++) {
        int u = defA[rndint(ca)];
        int v = defB[rndint(cb)];
        if (!has_edge(u, v)) {
            m->type = 2; m->a = u; m->b = v; m->c = 0; m->d = 0;
            apply_move(m);
            return 1;
        }
    }
    return 0;
}

static int propose_switch(Move *m) {
    int a = rndint(N);
    if (!deg[a]) return 0;
    int b = adj[a][rndint(deg[a])];
    int c = rndint(N);
    if (c == a || !deg[c] || side[c] != side[a]) return 0;
    int e = adj[c][rndint(deg[c])];
    if (e == b) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    m->type = 3; m->a = a; m->b = b; m->c = c; m->d = e;
    apply_move(m);
    return 1;
}

static void save_solution(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (u > v && m < ECAP) {
                sv_u[m] = v;
                sv_v[m] = u;
                m++;
            }
        }
    }
    sv_n = N;
    sv_m = m;
}

static void add_isolated(void) {
    side[N] = (int)(rnd64() & 1);
    deg[N] = 0;
    N++;
}

static void emit(int n, int m, const int *u, const int *v) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", u[i], v[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int maxgrow = (argc > 5) ? atoi(argv[5]) : 20;
    rng_s = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rng_s) rng_s = 1;
    DEG = d;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0 || m0 > ECAP || n0 < 0 || n0 >= NCAP) { printf("0 0\n"); return 0; }
    static int eu[ECAP], ev[ECAP];
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    /* Validate the start graph and build adjacency. */
    int ok = (DEG >= 1 && DEG <= DCAP && DIAM >= 1 && n0 >= 1);
    N = n0;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (has_edge(u, v)) { ok = 0; break; }
        if (deg[u] >= DEG || deg[v] >= DEG) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        for (int s = 0; s < N && ok; s++) {
            if (seen_[s]) continue;
            seen_[s] = 1;
            side[s] = 0;
            int h = 0, t = 0;
            qbuf[t++] = s;
            while (h < t && ok) {
                int x = qbuf[h++];
                for (int k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (!seen_[y]) {
                        seen_[y] = 1;
                        side[y] = 1 - side[x];
                        qbuf[t++] = y;
                    } else if (side[y] == side[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) {
        emit(n0, m0, eu, ev);
        return 0;
    }

    int grow_cap = n0 + maxgrow;
    if (grow_cap > NCAP - 1) grow_cap = NCAP - 1;
    if (maxgrow < 0) grow_cap = n0;

    /* The start graph is valid, so it is the fallback answer. */
    sv_n = n0;
    sv_m = m0;
    for (int i = 0; i < m0; i++) { sv_u[i] = eu[i]; sv_v[i] = ev[i]; }

    double t_start = now_s();
    double t_end = t_start + budget;
    long long cur = cost_fn();
    long long steps = 0, since = 0;
    int stop = 0;

    if (cur == 0) {
        save_solution();
        if (N >= grow_cap) stop = 1;
        else { add_isolated(); cur = cost_fn(); since = 0; }
    }

    while (!stop) {
        if ((steps & 127) == 0 && now_s() >= t_end) break;
        steps++;
        double T = TMIN + (T0 - TMIN) * exp(-(double)since / TAU);
        since++;
        Move mv;
        int got;
        double r = rnd01();
        if (r < 0.4) got = propose_rewire(&mv);
        else if (r < 0.7) got = propose_add(&mv);
        else got = propose_switch(&mv);
        if (!got) continue;

        long long nc = cost_fn();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) {
                save_solution();
                if (N >= grow_cap) break;
                add_isolated();
                cur = cost_fn();
                since = 0;
            }
        } else {
            undo_move(&mv);
        }
    }

    emit(sv_n, sv_m, sv_u, sv_v);
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


# ---------------------------------------------------------------- legacy driver (D != 3 or d < 3)

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


# ---------------------------------------------------------------- D = 3 driver (new)

def _build_d3(d, seed, time_limit):
    """D = 3, d >= 3: Moore-extremal PG(2,d-1) when d-1 is a prime power.

    Otherwise start from the best known base (Araujo-Pardo--Lopez graph for q = d-2 when
    q is a prime power, else PG(2,q) with q the largest prime power <= d-1) and let the
    C annealer search for larger valid graphs. Every candidate is checked with lib.is_valid,
    and the fallback is always a valid graph.
    """
    if lib.is_prime_power(d - 1):
        return _finish([lib.haar_graph(d, range(d)), lib.projective_plane_incidence(d - 1)], d, 3)

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: valid for D = 3
    start = cands[0]

    base = None
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            base = lib.araujo_lopez_graph(q)
        except Exception:
            base = None
    if base is None:
        try:
            base = _pg_base(d)
        except Exception:
            base = None
    if base is not None and lib.is_valid(base[0], base[1], d, 3):
        cands.append(base)
        start = base

    budget = max(0.5, C_TIME_FRAC * time_limit - 3.0)
    try:
        text = lib.run_c(C_SOURCE, [d, 3, seed, f"{budget:.2f}", MAX_GROW],
                         stdin_graph=start, timeout=time_limit * C_TIMEOUT_FRAC)
        cands.append(lib.parse_graph_text(text))
    except Exception:
        pass
    return _finish(cands, d, 3)


# ---------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if d >= 3 and D == 3:
        return _build_d3(d, seed, time_limit)
    return _legacy_build(d, D, seed, time_limit)
