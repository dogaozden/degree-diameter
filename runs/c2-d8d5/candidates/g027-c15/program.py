"""Bi-Cayley search: vertex-transitive bipartite lifts over semidirect products Z_m x| Z_k.

Graph: A_x ~ B_{x*s} for s in S (|S| = d). Left multiplication is an automorphism, so the
diameter condition reduces to two BFS runs (from A_e and from B_e). C anneals S over groups
of growing order until it fails to find a valid graph with more vertices than the start.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (calibration cases return immediately).
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# C engine: bi-Cayley annealing over semidirect products.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley search over Z_m x|_r Z_k.
 * Vertices: A_x = x (x < N), B_y = N + y. Edges A_x ~ B_{x*s} for s in S, |S| = d.
 * Left multiplication is an automorphism on each side, so validity is:
 *   BFS from A_e reaches all 2N vertices within D, and BFS from B_e reaches all 2N within D.
 * Usage:  prog d D seed time_limit lo
 *   lo = vertex count to beat. stdout: "n m" + edges of the best graph with n > lo, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2816
#define MAXD 64
#define GLCAP 4096
#define ITERS 15000

typedef struct { int m, k, r; } Grp;

static int d, D;
static double t_end;
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

static int gcd_i(int a, int b) {
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
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* All semidirect groups Z_m x|_r Z_k of order n: element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int enum_groups(int n, Grp *out, int cap) {
    int cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < cap) {
                out[cnt].m = m;
                out[cnt].k = k;
                out[cnt].r = r;
                cnt++;
            }
        }
    }
    return cnt;
}

static int N;
static int rp[MAXG];
static uint16_t MT[MAXG * MAXG];
static int INV[MAXG];
static int S[MAXD], SI[MAXD];
static int vis[2 * MAXG];
static int stamp = 0;
static int qu[2 * MAXG];

static void build_table(const Grp *G) {
    int m = G->m, k = G->k, r = G->r;
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int v = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
            MT[x * N + y] = (uint16_t)v;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Number of vertices reached from src within distance D. */
static int bfs_reach(int src) {
    stamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = stamp;
    int level_end = tail;
    for (int lev = 0; lev < D; lev++) {
        if (head == tail) break;
        while (head < level_end) {
            int v = qu[head++];
            if (v < N) {
                int base = v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + MT[base + S[i]];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            } else {
                int base = (v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = MT[base + SI[i]];
                    if (vis[u] != stamp) { vis[u] = stamp; qu[tail++] = u; }
                }
            }
        }
        level_end = tail;
    }
    return tail;
}

/* Number of unreached (source, target) pairs from A_e and B_e. Zero iff valid. */
static int cost(void) {
    return (2 * N - bfs_reach(0)) + (2 * N - bfs_reach(N));
}

static int in_set(int g, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == g) return 1;
    return 0;
}

static int anneal(int iters, double T0, double T1) {
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_set(g, i));
        S[i] = g;
        SI[i] = INV[g];
    }
    int cur = cost();
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now() > t_end) return 0;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i = rndint(d), g = rndint(N);
        if (in_set(g, d)) continue;
        int old = S[i], oldi = SI[i];
        S[i] = g;
        SI[i] = INV[g];
        int c = cost();
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
            cur = c;
            if (cur == 0) return 1;
        } else {
            S[i] = old;
            SI[i] = oldi;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit lo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    long want = lo / 2 + 1;
    if (want < d) want = d;
    int curN = (int)want;

    int bestN = 0;
    Grp bestG = {1, 1, 0};
    int bestS[MAXD];
    static Grp gl[GLCAP];

    while (now() < t_end) {
        if (2L * curN > moore || curN > MAXG) break;
        int ng = enum_groups(curN, gl, GLCAP);
        if (ng == 0) { curN++; continue; }
        Grp G = gl[rndint(ng < GLCAP ? ng : GLCAP)];
        build_table(&G);
        if (anneal(ITERS, 4.0, 0.2)) {
            bestN = curN;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * d);
            curN++;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_table(&bestG);
    for (int i = 0; i < d; i++) {
        S[i] = bestS[i];
        SI[i] = INV[S[i]];
    }
    if (cost() != 0) { printf("0 0\n"); return 0; }

    long m = (long)N * d;
    printf("%d %ld\n", 2 * N, m);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + (int)MT[x * N + S[i]]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for every D >= 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Replace best with (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    # Bi-Cayley annealing in C, aiming for more vertices than the current best.
    budget = 0.8 * time_limit - 4.0 - (time.monotonic() - t0)
    if D >= 2 and budget > 2.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                             timeout=budget + 6.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
