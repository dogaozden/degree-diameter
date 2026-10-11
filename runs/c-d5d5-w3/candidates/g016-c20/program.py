"""Bi-Cayley search: a different construction from the voltage-lift parent.

Python picks a valid start (K_{d,d}, or a known construction for D = 3 or 4) and calls the C engine.
C searches bi-Cayley graphs over semidirect products Z_m x| Z_k. For a group G and a d-subset S of G,
the graph has vertices A_g and B_g for g in G, with edges A_g -- B_{gs} for s in S. Each vertex has
degree d. Left multiplication is an automorphism, so diameter <= D holds iff BFS of depth D from A_e
and from B_e reaches every vertex. Each evaluation is therefore two BFS runs. S is annealed to minimise
unreached (source, vertex) pairs. The target order steps up by one group order at a time, with extra
escalation after repeated failures.

Trade-off: this replaces the parent's voltage-lift search and its orbit check with a different family
(bi-Cayley graphs with a single connection set). It is a high-risk variant. It may not reach the parent's
352 on d5D5. If it finds nothing larger than the start, C prints "0 0" and Python keeps the start, so every
case still returns a valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley degree-diameter search.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" header of a valid start graph (edges are ignored), or "0 0".
 * stdout:  "n m" then m lines "u v" for a bi-Cayley graph with more than n vertices,
 *          or "0 0" if none was found.
 *
 * Graph: group G = Z_m x| Z_k (order G), S = d distinct elements. Vertices A_g = g, B_g = G + g.
 * Edges A_g -- B_{g s} for s in S. Degree d, bipartite, simple.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXD 32
#define MAXN (2 * MAXG)

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

static int gcd_int(int a, int b) {
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

/* ------------------------------------------------------------ group tables */

static int GM, GK, GORD;
static int RP[MAXG];          /* RP[b] = r^b mod m */
static int MT[MAXG * MAXG];   /* MT[x*GORD + y] = x*y */
static int INV[MAXG];

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK + (b + e) % GK;
}

/* Element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Element 0 is the identity. */
static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GORD = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < GORD; x++)
        for (int y = 0; y < GORD; y++)
            MT[x * GORD + y] = gmul_raw(x, y);
    for (int x = 0; x < GORD; x++)
        for (int y = 0; y < GORD; y++)
            if (MT[x * GORD + y] == 0) { INV[x] = y; break; }
}

/* Uniform random semidirect group of order G among the sampled candidates (reservoir). */
static int sample_group(int G, int *om, int *ok, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k = G / m;
        if (m == 1 || k == 1) {
            if (rndint(++cnt) == 0) { *om = m; *ok = k; *orr = (m == 1) ? 0 : 1; }
            continue;
        }
        for (int t = 0; t < 60; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd_int(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { *om = m; *ok = k; *orr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ bi-Cayley cost */

static int S[MAXD];
static char INS[MAXG];
static int QU[MAXN];
static int VIS[MAXN];
static int VST = 0;

/* Unreached (source, vertex) pairs from A_e and B_e. Zero means diameter <= D. */
static long cost(void) {
    int G = GORD, N = 2 * G;
    long total = 0;
    for (int src = 0; src < 2; src++) {
        if (++VST == 0x7fffffff) { memset(VIS, 0, sizeof VIS); VST = 1; }
        int head = 0, tail = 0;
        int s0 = src * G;
        VIS[s0] = VST;
        QU[tail++] = s0;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                if (u < G) {
                    /* A_g: neighbours B_{g s}. */
                    for (int i = 0; i < d; i++) {
                        int v = G + MT[u * G + S[i]];
                        if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                    }
                } else {
                    /* B_h: neighbours A_{h s^-1}. */
                    int h = u - G;
                    for (int i = 0; i < d; i++) {
                        int v = MT[h * G + INV[S[i]]];
                        if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

/* Anneal the connection set S in the current group. Returns 1 on success, 0 on failure, -1 on timeout. */
static int anneal(long steps) {
    int G = GORD;
    memset(INS, 0, sizeof INS);
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(G); } while (INS[x]);
        S[i] = x;
        INS[x] = 1;
    }
    long c = cost();
    for (long s = 0; s < steps && c > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) return -1;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int i = rndint(d);
        int x = rndint(G);
        if (INS[x]) continue;
        int old = S[i];
        INS[old] = 0;
        INS[x] = 1;
        S[i] = x;
        long c2 = cost();
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            INS[x] = 0;
            INS[old] = 1;
            S[i] = old;
        }
    }
    return c == 0 ? 1 : 0;
}

/* ------------------------------------------------------------ output */

static void print_bicayley(int G, const int *Sset) {
    long m = (long)G * d;
    printf("%d %ld\n", 2 * G, m);
    for (int g = 0; g < G; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, G + MT[g * G + Sset[i]]);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    int start_n = 0, start_m = 0;
    if (scanf("%d %d", &start_n, &start_m) != 2) start_n = 0;
    int best_n = start_n > 2 * d ? start_n : 2 * d;

    long moore = moore_bound();
    int found = 0, bm = 0, bk = 0, br = 0, bG = 0;
    int bS[MAXD];
    int fails = 0;

    while (now() < t_end) {
        int G0 = best_n / 2 + 1;
        if (G0 > MAXG || 2L * G0 > moore) break;
        int esc = fails / 30;
        if (esc > 3) esc = 3;
        int G = G0 + rndint(2) + esc;
        if (G > MAXG || 2L * G > moore || G < d + 1) G = G0;
        if (G < d + 1) G = d + 1;
        if (G > MAXG || 2L * G > moore) break;

        int m, k, r;
        if (!sample_group(G, &m, &k, &r)) { fails++; continue; }
        set_group(m, k, r);

        long extra = (long)(fails / 20) * 3000;
        if (extra > 40000) extra = 40000;
        long steps = 3000 + rndint(6000) + extra;

        int res = anneal(steps);
        if (res < 0) break;
        if (res == 1) {
            found = 1;
            best_n = 2 * G;
            bm = m; bk = k; br = r; bG = G;
            memcpy(bS, S, sizeof(int) * d);
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!found) { printf("0 0\n"); return 0; }

    /* Re-verify the best construction before printing. */
    set_group(bm, bk, br);
    memcpy(S, bS, sizeof(int) * d);
    if (cost() != 0) { printf("0 0\n"); return 0; }
    print_bicayley(bG, bS);
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

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
