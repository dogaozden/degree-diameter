import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite edge-toggle annealer with vertex growth (unchanged).
# It takes a start graph on stdin, anneals bad-pair cost to zero, and grows
# the graph by vertex pairs while it stays valid.
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

/* Ordered pairs (u, v) with distance > D_. Zero means the graph is valid. */
static long long bad_pairs(void) {
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
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
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
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
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
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
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
# New construction: abelian Haar graphs (bi-Cayley graphs over Z_m1 x Z_m2).
#
# Vertices a_g and b_h for g, h in G = Z_m1 x Z_m2; a_g ~ b_{g+s} for s in S,
# |S| = d. This is d-regular and bipartite. The graph is symmetric under
# translations and under swapping sides, so its diameter is at most D exactly
# when every vertex is within distance D of a_0. We search over S by simulated
# annealing, with a numpy level-set BFS as the cost (unreached vertices).
# ----------------------------------------------------------------------------

def _haar_cost(m1, m2, S, D):
    """Number of vertices not within distance D of a_0 (0 means diameter <= D)."""
    A = np.zeros((m1, m2), dtype=bool)
    B = np.zeros((m1, m2), dtype=bool)
    A[0, 0] = True
    for step in range(D):
        if step % 2 == 0:
            new = B.copy()
            for si, sj in S:
                new |= np.roll(A, (si, sj), axis=(0, 1))
            B = new
        else:
            new = A.copy()
            for si, sj in S:
                new |= np.roll(B, (-si, -sj), axis=(0, 1))
            A = new
    return int(A.size - A.sum()) + int(B.size - B.sum())


def _haar_search(d, D, m1, m2, rng, deadline):
    """Anneal a connection set S (size d) in Z_m1 x Z_m2. Returns S as (si, sj) pairs, or None."""
    G = m1 * m2
    if d > G:
        return None
    chosen = rng.sample(range(G), d)
    inS = set(chosen)
    S = [(x // m2, x % m2) for x in chosen]
    cost = _haar_cost(m1, m2, S, D)
    if cost == 0:
        return S
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = max(1.0, 0.05 * cost)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return None
        if len(inS) >= G:
            return None
        frac = (now - start) / span
        T = 0.05 + T0 * (1.0 - frac)
        k = rng.randrange(d)
        x = rng.randrange(G)
        while x in inS:
            x = rng.randrange(G)
        old_idx, old_el = chosen[k], S[k]
        S[k] = (x // m2, x % m2)
        c2 = _haar_cost(m1, m2, S, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            inS.discard(old_idx)
            inS.add(x)
            chosen[k] = x
            if cost == 0:
                return S
        else:
            S[k] = old_el


def _haar_edges(m1, m2, S):
    """Edge list of the Haar graph: vertices a_g = g and b_h = G + h."""
    G = m1 * m2
    edges = []
    for g in range(G):
        gi, gj = divmod(g, m2)
        for si, sj in S:
            h = ((gi + si) % m1) * m2 + (gj + sj) % m2
            edges.append((g, G + h))
    return 2 * G, edges


def _haar_attempt(d, D, m, rng, budget):
    """Try to find a d-regular Haar graph with 2m vertices. Returns (n, edges) or None."""
    deadline = time.monotonic() + budget
    divs = [k for k in range(1, 13) if m % k == 0 and m // k >= d]
    if not divs:
        return None
    m2 = rng.choice(divs)
    m1 = m // m2
    S = _haar_search(d, D, m1, m2, rng, deadline)
    if S is None:
        return None
    return _haar_edges(m1, m2, S)


# ----------------------------------------------------------------------------
# Known exact or record-type constructions (used for calibration and as seeds).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    # Exact constructions. For d3D3 this returns immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2) and not lib.is_prime_power(d - 1):
            try:
                an, ae = lib.araujo_lopez_graph(d - 2)
                consider(an, ae)
            except Exception:
                pass

    # Phase 1 (bold): search abelian Haar graphs of growing size.
    # Each success is validated by consider(); on failure the step shrinks.
    haar_deadline = t0 + max(1.0, 0.6 * (time_limit - 6.0))
    attempt_budget = max(1.0, 0.1 * time_limit)
    lo = max(d, best[0] // 2)
    step = 1
    while True:
        rem = haar_deadline - time.monotonic()
        if rem < 0.5:
            break
        m = lo + step
        res = _haar_attempt(d, D, m, rng, min(attempt_budget, rem))
        if res is not None and consider(res[0], res[1]):
            lo = m
            step *= 2
            continue
        if step == 1:
            break
        step //= 2

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
    rem = t0 + time_limit - 6.0 - time.monotonic() - 1.0
    if rem >= 2.0 and best[0] >= 4:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, rem,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
