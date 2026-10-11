"""Bi-Cayley search over semidirect product groups, replacing the voltage-lift engine.

Construction: pick a finite group G (a semidirect product Z_m x|_r Z_k, order G) and a connection
set S of d distinct elements. The bi-Cayley graph has vertices (x, 0) and (x, 1) for x in G, and
edges (x, 0)-(x*s, 1) for s in S. It is bipartite and d-regular. Left multiplication is an
automorphism that is transitive on each side, so diameter <= D holds iff a BFS of depth D from
(e,0) and from (e,1) reaches every vertex. That is two BFS runs per evaluation.

Search: simulated annealing over S minimizes the number of unreached pairs. The target order G
climbs upward: each success raises the bar, and failures lengthen the annealing runs. The C engine
ignores stdin and prints the largest bi-Cayley graph it found, or "0 0". Python keeps the known
construction or K_{d,d} as a fallback and only accepts a C result that is larger and passes lib.is_valid.
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

#define MAXG 1024
#define MAXD 32

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static int GM, GK, GR, GN;
static int RP[MAXG];
static int MT[MAXG][MAXG];
static int INV[MAXG];

static int slow_mul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    long t = ((long)a + (long)RP[b] * c) % GM;
    return (int)(t * GK + (b + e) % GK);
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) MT[x][y] = slow_mul(x, y);
    for (int x = 0; x < GN; x++) {
        INV[x] = 0;
        for (int y = 0; y < GN; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
    }
}

/* Random semidirect group of order N: reservoir sampling over candidates (m, k, r). */
static int sample_group(int N, int *om, int *ok, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (k < 1) continue;
        if (m == 1 || k == 1) {
            int r = (m == 1) ? 0 : 1;
            if (rndint(++cnt) == 0) { *om = m; *ok = k; *orr = r; }
            continue;
        }
        for (int t = 0; t < 60; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ bi-Cayley check */

static int S[MAXD], SI[MAXD];      /* connection set and its inverses */
static int mark[2 * MAXG];
static int stampv = 0;
static int Q[2 * MAXG];

/* Unreached (source, vertex) pairs for sources (e,0) and (e,1). Zero means diameter <= D. */
static long cost_of(void) {
    int N = 2 * GN;
    long total = 0;
    for (int src = 0; src < 2; src++) {
        stampv++;
        int head = 0, tail = 0;
        int s0 = src * GN;
        mark[s0] = stampv;
        Q[tail++] = s0;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = Q[head++];
                if (u < GN) {
                    for (int t = 0; t < d; t++) {
                        int v = GN + MT[u][S[t]];
                        if (mark[v] != stampv) { mark[v] = stampv; Q[tail++] = v; }
                    }
                } else {
                    int y = u - GN;
                    for (int t = 0; t < d; t++) {
                        int v = MT[y][SI[t]];
                        if (mark[v] != stampv) { mark[v] = stampv; Q[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void random_set(void) {
    for (int t = 0; t < d; t++) {
        int v, ok;
        do {
            v = rndint(GN);
            ok = 1;
            for (int j = 0; j < t; j++)
                if (S[j] == v) { ok = 0; break; }
        } while (!ok);
        S[t] = v;
        SI[t] = INV[v];
    }
}

/* One annealing run over connection sets in the current group. Returns 1 on success
 * (out holds S), 0 on failure, -1 on timeout. */
static int anneal(long steps, int *out) {
    random_set();
    long cur = cost_of();
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 127) == 0 && now() > t_end) return -1;
        double T = 1.0 * (1.0 - (double)s / (double)steps) + 0.03;
        int t = rndint(d);
        int nv = rndint(GN);
        int dup = 0;
        for (int j = 0; j < d; j++)
            if (S[j] == nv) { dup = 1; break; }
        if (dup) continue;
        int old = S[t], oldi = SI[t];
        S[t] = nv;
        SI[t] = INV[nv];
        long c2 = cost_of();
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            S[t] = old;
            SI[t] = oldi;
        }
    }
    if (cur == 0) {
        for (int t = 0; t < d; t++) out[t] = S[t];
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ main */

static int bestG = 0, bestM = 0, bestK = 0, bestR = 0;
static int bestSet[MAXD];
static int tmpSet[MAXD];

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_group]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long cap = moore / 2;
    if (cap > MAXG) cap = MAXG;
    if (cap < d) { printf("0 0\n"); return 0; }
    if (lo < d) lo = d;
    if (lo > cap) lo = (int)cap;

    int fails = 0;
    while (now() < t_end && bestG < cap) {
        if (bestG == 0 && fails > 0 && fails % 300 == 0 && lo > d) lo--;
        int G;
        if (bestG == 0) G = lo + rndint(3);
        else G = bestG + 1 + rndint(3);
        if (G > cap) G = (int)cap;
        if (G < d) G = d;

        int m, k, r;
        if (!sample_group(G, &m, &k, &r)) { fails++; continue; }
        long steps = 5000 + rndint(5000) + (long)fails * 150;
        if (steps > 300000) steps = 300000;
        set_group(m, k, r);
        int res = anneal(steps, tmpSet);
        if (res < 0) break;
        if (res == 1 && G > bestG) {
            bestG = G;
            bestM = m;
            bestK = k;
            bestR = r;
            memcpy(bestSet, tmpSet, sizeof(int) * (size_t)d);
            fails = 0;
        } else {
            fails++;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }

    /* Final verification of the best connection set before printing. */
    set_group(bestM, bestK, bestR);
    for (int t = 0; t < d; t++) {
        S[t] = bestSet[t];
        SI[t] = INV[bestSet[t]];
    }
    if (cost_of() != 0) { printf("0 0\n"); return 0; }

    int G = bestG;
    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, G + MT[x][S[t]]);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    # Start the group-order climb near the expected range, not at the trivial value.
    lower = max(best[0] // 2 + 1, int(0.4 * moore / 2))
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lower],
                         stdin_graph=None, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
