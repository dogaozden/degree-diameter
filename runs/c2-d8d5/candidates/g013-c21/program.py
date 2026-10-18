import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite edge-toggle annealer with vertex growth (unchanged).
#
# The state is a bipartite graph with max degree d. A move toggles one
# cross-side pair (a, b): if a or b is full, one of its edges is dropped
# first. The cost is the number of ordered vertex pairs at distance > D,
# computed with bitset ball expansion. Per-vertex unreached counts are kept
# for the current state, and roughly half of the proposed endpoints are drawn
# from vertices that still have unreached pairs. Whenever the cost reaches
# zero, the current valid graph is saved and two isolated vertices (one per
# side) are added, so the search keeps growing the graph while time remains.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int *bvCur, *bvNew;   /* per-vertex unreached counts: current state / candidate */
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

/* Fills out[v] = number of vertices at distance > D_ from v. Returns the sum
   over v (ordered pairs at distance > D_). Zero means the graph is valid. */
static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

/* Biased endpoint choice: often pick a vertex that still has unreached pairs. */
static int pick_vertex(void) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bvCur[v] > 0) return v;
        }
    }
    return rint_(N);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bvCur = malloc(sizeof(int) * (size_t)cap_n);
    bvNew = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    /* Bipartition by BFS; isolated vertices take the side of their root. */
    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(), y = pick_vertex();
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
#
# New construction for this island: multi-orbit CYCLIC lifts. Take a base
# bipartite graph with k vertices per side, realised as d "layers". Layer l
# matches A-vertex i to B-vertex P_l[i] (P_l a permutation) with voltage S_l[i]
# in Z_m, so A(i,x) ~ B(P_l[i], x + S_l[i]). Every vertex then has degree d and
# the graph has 2*k*m vertices. Diameter is checked for all pairs by evaluating
# only the 2k base vertices (the lift is Z_m-invariant). The reach test is a
# vectorised boolean BFS over all sources at once, because each layer is a
# perfect matching and its partner map is an involution.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _nbr(k, m, d, P, S):
    """Partner table nbr[l, v] for the cyclic lift. A(i,x) = i*m+x, B(j,y) = (k+j)*m+y."""
    N = 2 * k * m
    X = np.arange(m, dtype=np.int64)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        p = P[l]
        s = S[l]
        pinv = np.argsort(p)
        for i in range(k):
            nbr[l, i * m:(i + 1) * m] = (k + int(p[i])) * m + (X + int(s[i])) % m
        for j in range(k):
            i = int(pinv[j])
            nbr[l, (k + j) * m:(k + j + 1) * m] = i * m + (X - int(s[i])) % m
    return nbr


def _lift_cost(nbr, D, srcs):
    """Total unreached pairs from the base sources. Zero iff the lift has diameter <= D."""
    S_ = len(srcs)
    N = nbr.shape[1]
    F = np.zeros((S_, N), dtype=bool)
    F[np.arange(S_), srcs] = True
    vis = F.copy()
    for _ in range(D):
        new = np.zeros((S_, N), dtype=bool)
        for l in range(nbr.shape[0]):
            new |= F[:, nbr[l]]
        new &= ~vis
        if not new.any():
            break
        vis |= new
        F = new
    return int((N - vis.sum(axis=1)).sum())


def _lift_edges(nbr, k, m):
    """Undirected edge list of the lift; A-vertices are ids below k*m."""
    E = set()
    for l in range(nbr.shape[0]):
        for v in range(k * m):
            E.add((v, int(nbr[l, v])))
    return sorted(E)


def _lift_search(d, D, k, m, rng, deadline, iters, patience):
    """Hill climbing over layer permutations and voltages. Returns (n, edges) or None."""
    N = 2 * k * m
    srcs = np.arange(2 * k, dtype=np.int64) * m
    P = [np.array(rng.sample(range(k), k), dtype=np.int64) for _ in range(d)]
    S = [np.array([rng.randrange(m) for _ in range(k)], dtype=np.int64) for _ in range(d)]
    cur = _lift_cost(_nbr(k, m, d, P, S), D, srcs)
    c0 = float(max(cur, 1))
    best = cur
    last = 0
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.2, 0.1 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        if k >= 2 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            P[l][[i1, i2]] = P[l][[i2, i1]]
            c2 = _lift_cost(_nbr(k, m, d, P, S), D, srcs)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
                cur = c2
                if cur < best:
                    best, last = cur, t
            else:
                P[l][[i1, i2]] = P[l][[i2, i1]]
        else:
            i = rng.randrange(k)
            old = int(S[l][i])
            S[l][i] = rng.randrange(m)
            c2 = _lift_cost(_nbr(k, m, d, P, S), D, srcs)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
                cur = c2
                if cur < best:
                    best, last = cur, t
            else:
                S[l][i] = old
    if cur != 0:
        return None
    nbr = _nbr(k, m, d, P, S)
    return N, _lift_edges(nbr, k, m)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: multi-orbit cyclic lifts with a bandit over base sizes k.
    p1_end = t0 + max(1.0, min(0.55 * time_limit, time_limit - 14.0))
    ks = [1, 2, 3, 4, 6]
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < p1_end:
        k = pick_k()
        m_min = -(-(best[0] + 2) // (2 * k))
        m = max(2, m_min + rng.randrange(0, 3))
        trials[k] += 1
        res = _lift_search(d, D, k, m, rng, p1_end, 2500, 500)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: use spare degree in the current best graph.
    slack_end = t0 + max(1.0, min(0.65 * time_limit, time_limit - 10.0))
    if time.monotonic() < slack_end:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
        consider(n2, e2)

    # Phase 3: C annealer grows the best valid graph by vertex pairs.
    c_budget = time_limit - (time.monotonic() - t0) - 7.0
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
