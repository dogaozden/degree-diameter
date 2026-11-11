"""Random-regular switch annealing for bipartite graphs with bounded diameter.

Different construction from the bi-Cayley parent: no group structure. The C engine starts
from a circulant d-regular bipartite graph on h+h vertices, randomises it with double-edge
switches, and anneals switches to minimise the number of vertex pairs at distance > D
(bitset ball expansion). A ladder over h raises the order after each success.

Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) as the
fallback. The C output is accepted only if it passes lib.is_valid and has more vertices.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 8
#define MAXW (MAXN / 64)
#define MAXH (MAXN / 2)

static int d, D, h, n;
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int bestn = 0;
static int bestadj[MAXN][MAXD];
static int bestdeg[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static long MOORE;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == old) { adj[v][k] = nw; return; }
}

/* Number of unordered pairs at distance > D. */
static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

/* Circulant start: A-vertex a adjacent to B-vertex h + (a+s) mod h, s = 0..d-1. */
static void init_graph(void) {
    n = 2 * h;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int a = 0; a < h; a++)
        for (int s = 0; s < d; s++) {
            int b = h + (a + s) % h;
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
}

/* Double-edge switch: (a,b1),(a2,b2) -> (a,b2),(a2,b1). Returns 0 and changes nothing if invalid. */
static int apply_sw(int a, int i, int a2, int j) {
    int b1 = adj[a][i], b2 = adj[a2][j];
    if (a == a2 || b1 == b2) return 0;
    if (has_edge(a, b2) || has_edge(a2, b1)) return 0;
    adj[a][i] = b2;
    adj[a2][j] = b1;
    repl(b1, a, a2);
    repl(b2, a2, a);
    return 1;
}

static void undo_sw(int a, int i, int a2, int j) {
    int x = adj[a][i], y = adj[a2][j];   /* x = old b2, y = old b1 */
    adj[a][i] = y;
    adj[a2][j] = x;
    repl(y, a2, a);
    repl(x, a, a2);
}

static void randomize(void) {
    long its = 20L * h * d;
    for (long it = 0; it < its; it++)
        apply_sw(rndint(h), rndint(d), rndint(h), rndint(d));
}

static int anneal(double until) {
    long cur = bad_pairs();
    double T = 0.5;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int a = rndint(h), i = rndint(d), a2 = rndint(h), j = rndint(d);
        if (!apply_sw(a, i, a2, j)) continue;
        long nb = bad_pairs();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
        else undo_sw(a, i, a2, j);
        T *= 0.9995;
        if (T < 0.05) T = 0.5;
    }
    return 1;
}

static int attempt(int hh, double until) {
    h = hh;
    init_graph();
    randomize();
    if (!anneal(until)) return 0;
    bestn = n;
    memcpy(bestadj, adj, sizeof adj);
    memcpy(bestdeg, deg, sizeof deg);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit h0\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int h0 = atoi(argv[5]);
    double t0 = now();
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    MOORE = moore_bound();
    if (h0 < d) h0 = d;

    int base = 0, step = 1, hh = h0;
    while (now() < t_end) {
        if (2L * hh > MOORE || hh > MAXH) break;
        double left = t_end - now();
        double sl = left / 3;
        if (sl < 1.0) sl = 1.0;
        if (sl > left) sl = left;
        if (attempt(hh, now() + sl)) {
            base = hh;
            if (step < 128) step *= 2;
        } else if (step > 1) {
            step /= 2;
        }
        hh = (base > 0) ? base + step : h0;
    }

    if (bestn == 0) { printf("0 0\n"); return 0; }
    long m = 0;
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bestdeg[u]; k++)
            if (u < bestadj[u][k]) m++;
    printf("%d %ld\n", bestn, m);
    for (int u = 0; u < bestn; u++)
        for (int k = 0; k < bestdeg[u]; k++)
            if (u < bestadj[u][k]) printf("%d %d\n", u, bestadj[u][k]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    h0 = max(d, best[0] // 2 + 1)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, h0], timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
