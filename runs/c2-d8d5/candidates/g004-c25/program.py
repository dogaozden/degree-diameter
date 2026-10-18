"""Bipartite Cayley ("bi-coset") graphs over semidirect products Z_m x| Z_k, searched in C.

Vertices (g,0) = g and (g,1) = N+g for a group G of order N. Each (g,0) is joined to (g*s,1)
for s in a d-element set S, so the graph is d-regular and bipartite. Left multiplication is an
automorphism that preserves both sides, so the diameter is at most D iff BFS from (e,0) and
from (e,1) reaches all 2N vertices within D steps. The C engine picks a random group of order N
and anneals S to cover everything, then grows N.
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

/* Usage: prog d D seed time_limit  (stdin ignored). Prints a bipartite Cayley graph. */

#define MAXG 3000
#define MAXDEG 40

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 0x2545F4914F6CDD1DULL;
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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Z_m x|_r Z_k with element (a,b) = a*k+b and (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int N, m, k, r;
    int *M;     /* M[x*N+y] = x*y */
    int *inv;
    int rp[MAXG];
} Group;

static void free_group(Group *G) {
    free(G->M);
    free(G->inv);
    G->M = NULL;
    G->inv = NULL;
}

static int build_group(Group *G, int m, int k, int r) {
    int N = m * k;
    G->N = N; G->m = m; G->k = k; G->r = r;
    G->M = malloc(sizeof(int) * (size_t)N * N);
    G->inv = malloc(sizeof(int) * (size_t)N);
    if (!G->M || !G->inv) return 0;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            G->M[(size_t)x * N + y] = (int)((a + (long)G->rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (G->M[(size_t)x * N + y] == 0) { G->inv[x] = y; break; }
    return 1;
}

/* Uniform random choice among all (m,k,r) with m*k = N. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    *pm = bm; *pk = bk; *pr = br;
    return 1;
}

static int *mark_arr;
static int *q_arr;
static int mark_stamp = 0;

/* Number of vertices NOT within distance D of source (e, src_side). */
static int unreached_from(const Group *G, const int *S, const int *Si, int src_side) {
    int N = G->N, V = 2 * N;
    const int *M = G->M;
    mark_stamp++;
    int head = 0, tail = 0, reached = 1;
    int src = src_side ? N : 0;
    mark_arr[src] = mark_stamp;
    q_arr[tail++] = src;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = q_arr[head++];
            if (v < N) {
                const int *row = M + (size_t)v * N;
                for (int j = 0; j < d; j++) {
                    int u = N + row[S[j]];
                    if (mark_arr[u] != mark_stamp) {
                        mark_arr[u] = mark_stamp;
                        q_arr[tail++] = u;
                        reached++;
                    }
                }
            } else {
                const int *row = M + (size_t)(v - N) * N;
                for (int j = 0; j < d; j++) {
                    int u = row[Si[j]];
                    if (mark_arr[u] != mark_stamp) {
                        mark_arr[u] = mark_stamp;
                        q_arr[tail++] = u;
                        reached++;
                    }
                }
            }
        }
    }
    return V - reached;
}

static int cost_of(const Group *G, const int *S, const int *Si) {
    return unreached_from(G, S, Si, 0) + unreached_from(G, S, Si, 1);
}

static int in_set(const int *S, int cnt, int x) {
    for (int i = 0; i < cnt; i++) if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over S (d distinct group elements). Returns 1 on success,
 * 0 on failure, -1 on timeout. On success S and Si hold the solution. */
static int anneal(const Group *G, int *S, int *Si, long steps) {
    int N = G->N;
    for (int j = 0; j < d; j++) {
        int x;
        do { x = rndint(N); } while (in_set(S, j, x));
        S[j] = x;
        Si[j] = G->inv[x];
    }
    int cost = cost_of(G, S, Si);
    for (long t = 0; t < steps && cost > 0; t++) {
        if ((t & 31) == 0 && now() > t_end) return -1;
        int j = rndint(d);
        int x = rndint(N);
        if (in_set(S, d, x)) continue;
        int old = S[j], oldi = Si[j];
        S[j] = x;
        Si[j] = G->inv[x];
        int c2 = cost_of(G, S, Si);
        double T = 1.5 * (1.0 - (double)t / (double)steps) + 0.05;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            S[j] = old;
            Si[j] = oldi;
        }
    }
    return cost == 0;
}

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 1 || D < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    if (D == 1) {
        printf("2 1\n0 1\n");
        return 0;
    }
    mark_arr = calloc(2 * MAXG, sizeof(int));
    q_arr = calloc(2 * MAXG, sizeof(int));
    long moore = moore_bound();

    int bestN = d, bm = 1, bk = d, br = 0;
    int bS[MAXDEG];
    for (int j = 0; j < d; j++) bS[j] = j;

    static Group G;
    int S[MAXDEG], Si[MAXDEG];
    while (now() < t_end) {
        int window = 1 + bestN / 50;
        int N = bestN + 1 + rndint(window);
        if (N > MAXG || 2L * N > moore) {
            N = bestN + 1;
            if (N > MAXG || 2L * N > moore) break;
        }
        int m, k, r;
        if (!pick_group(N, &m, &k, &r)) continue;
        free_group(&G);
        if (!build_group(&G, m, k, r)) break;
        int res = anneal(&G, S, Si, 4000);
        if (res < 0) break;
        if (res == 1) {
            bestN = N;
            bm = m; bk = k; br = r;
            memcpy(bS, S, sizeof(int) * d);
        }
    }
    free_group(&G);

    static Group H;
    int ok = build_group(&H, bm, bk, br);
    if (ok) {
        int Si2[MAXDEG];
        for (int j = 0; j < d; j++) Si2[j] = H.inv[bS[j]];
        ok = (cost_of(&H, bS, Si2) == 0);
    }
    if (!ok) {
        print_complete();
        return 0;
    }
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, N + H.M[(size_t)g * N + bS[j]]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for the calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bipartite Cayley graphs over semidirect products, in C.
    if D >= 2 and time_limit > 6:
        elapsed = time.monotonic() - t0
        budget = max(1.0, 0.8 * time_limit - 3.0 - elapsed)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=None, timeout=budget + 10)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
