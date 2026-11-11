"""Unstructured search for d-regular bipartite graphs with diameter at most D.

Stage 0 is a safe fallback: K_{d,d} or an algebraic start (projective plane, Araujo-Pardo-Lopez,
or the generalized quadrangle W(q) for D >= 4).

The new construction does not use groups. The C engine takes a target N per side, starts from the
circulant d-regular bipartite graph A_a ~ B_{a+k mod N}, and anneals with degree-preserving
2-switches. The cost is the number of ordered vertex pairs at distance more than D. Distances come
from bitset ball expansion (D rounds of OR over neighbours), so one evaluation is O(V d W) word
operations. Python raises N each time a valid graph is found, and it halves the step after a
failed attempt. The largest valid graph is returned, and the algebraic fallback always remains.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1600
#define MAXD 8
#define MAXV (2 * MAXN)
#define MAXW ((MAXV + 63) / 64)

static int d, D, N, V, W;
static int adj[MAXV * MAXD];
static uint64_t bufA[MAXV * MAXW], bufB[MAXV * MAXW];
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Number of ordered pairs (v, u) with dist(v, u) > D. Zero iff the graph is valid. */
static long eval_cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * W);
    for (int v = 0; v < V; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int k = 0; k < d; k++) {
                const uint64_t *nb = cur + (size_t)adj[v * d + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
            for (int w = 0; w < W; w++)
                if (dst[w] != src[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long unr = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        unr += V - c;
    }
    return unr;
}

/* Vertices: A-side ids 0..N-1, B-side ids N..2N-1. */
static void init_graph(void) {
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++)
            adj[a * d + k] = N + (a + k) % N;
    for (int b = 0; b < N; b++)
        for (int k = 0; k < d; k++)
            adj[(N + b) * d + k] = (b - k + N) % N;
}

static int has_edge(int a, int x) {
    for (int k = 0; k < d; k++)
        if (adj[a * d + k] == x) return 1;
    return 0;
}

static int find_slot(int x, int a) {
    for (int k = 0; k < d; k++)
        if (adj[x * d + k] == a) return k;
    return -1;
}

/* Propose a 2-switch: (a1,x1),(a2,x2) -> (a1,x2),(a2,x1). Keep it if accepted by SA. */
static long try_move(long cur, double T) {
    int a1 = rndint(N), k1 = rndint(d);
    int a2 = rndint(N), k2 = rndint(d);
    if (a1 == a2) return cur;
    int x1 = adj[a1 * d + k1], x2 = adj[a2 * d + k2];
    if (x1 == x2) return cur;
    if (has_edge(a1, x2) || has_edge(a2, x1)) return cur;
    int j1 = find_slot(x1, a1), j2 = find_slot(x2, a2);
    if (j1 < 0 || j2 < 0) return cur;

    adj[a1 * d + k1] = x2;
    adj[a2 * d + k2] = x1;
    adj[x1 * d + j1] = a2;
    adj[x2 * d + j2] = a1;

    long nc = eval_cost();
    long delta = nc - cur;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) return nc;

    adj[a1 * d + k1] = x1;
    adj[a2 * d + k2] = x2;
    adj[x1 * d + j1] = a1;
    adj[x2 * d + j2] = a2;
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit N_half\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long n = atol(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double t_end = t0 + limit * 0.92;
    if (d < 3 || d > MAXD || D < 2 || n < d + 1 || n > MAXN) {
        printf("0 0\n");
        return 0;
    }
    N = (int)n;
    V = 2 * N;
    W = (V + 63) / 64;
    init_graph();
    long cur = eval_cost();

    double ts = now();
    double span = t_end - ts;
    if (span < 0.1) span = 0.1;
    const double T0 = 6.0, T1 = 0.25;
    while (cur > 0) {
        double tn = now();
        if (tn >= t_end) break;
        double frac = (tn - ts) / span;
        double ph = frac * 4.0;          /* four reheating cycles */
        ph -= floor(ph);
        double T = T0 * pow(T1 / T0, ph);
        cur = try_move(cur, T);
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", V, N * d);
    for (int a = 0; a < N; a++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", a, adj[a * d + k]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} or the best algebraic start.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 8 or best[0] >= moore:
        return best

    deadline = t0 + 0.85 * time_limit - 1.0
    cap_half = min(1600, moore // 2)
    best_half = best[0] // 2
    step = max(1, best_half // 100)
    it = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        N = best_half + step
        if N > cap_half:
            N = cap_half
        if N <= best_half or N < d + 1:
            break
        slice_ = min(remaining, max(3.0, 0.4 * remaining))
        it += 1
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 1000 + it, round(slice_, 2), N],
                             stdin_graph=None, timeout=slice_ + 10)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_half = n // 2
                continue
        except Exception:
            pass
        if N >= cap_half:
            break
        step = max(1, step // 2)
    return best
