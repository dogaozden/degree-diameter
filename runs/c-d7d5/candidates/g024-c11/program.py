"""Bold variant for the d7 D5 target: a simulated-annealing bi-Cayley search.

Instead of breakout local search, this version anneals the voltage assignment
(dart connection elements and, for K >= 2, the per-dart permutations) over
semidirect groups Z_m x| Z_k. Cost is exact: the group acts by left
multiplication, so it suffices to check distances from the 2K representative
vertices, which is done with 64-bit reachability masks. Untested here; the
exact baselines and the K_{d,d} fallback guarantee a valid return either way.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent).
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
# C engine: simulated annealing over bi-Cayley voltage lifts.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# Dart l with permutation P[l] (i -> j) and element S[l][i] gives edges
# A_{i,g} -- B_{P[l][i], g*S[l][i]} for all g. Every vertex then has exactly
# one neighbour per dart, so the degree is Dd.
#
# Cost = (number of (source, vertex) pairs at distance > DD, over the 2K
# source vertices A_{i,e}, B_{j,e}) + PEN * (duplicate darts).
# Exact because left multiplication by G is an automorphism.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 3
#define PEN 1000
#define MAXG 20000

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 7, DD = 5;
static double deadline = 0.0;

static int GM = 1, GK = 1, GG = 1;
static int gpow[256];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Semidirect product Z_m x| Z_k: (a,b)(c,d) = (a + r^b c, b + d), coded a*k+b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, d = y - c * GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    int e = b + d;
    if (e >= GK) e -= GK;
    return (int)t * GK + e;
}

static int capN = 0;
static int *adj = NULL;          /* adj[v*MAXD + l] = neighbour of v via dart l */
static uint64_t *reachA = NULL, *reachB = NULL;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(reachA);
    free(reachB);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * MAXD);
    reachA = malloc(sizeof(uint64_t) * (size_t)N);
    reachB = malloc(sizeof(uint64_t) * (size_t)N);
    if (!adj || !reachA || !reachB) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static void rebuild_dart(const Cfg *c, int l) {
    int K = c->K, G = GG;
    for (int i = 0; i < K; i++) {
        int j = c->P[l][i], s = c->S[l][i];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            adj[a * MAXD + l] = b;
            adj[b * MAXD + l] = a;
        }
    }
}

static void rebuild_all(const Cfg *c) {
    for (int l = 0; l < Dd; l++) rebuild_dart(c, l);
}

static int count_dups(const Cfg *c) {
    int dup = 0;
    for (int i = 0; i < c->K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    return dup;
}

static int popc64(uint64_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

/* Unreached (source, vertex) pairs within DD steps, using bitmasks over sources. */
static long long bfs_raw(int K) {
    int G = GG, N = 2 * K * G, nsrc = 2 * K;
    uint64_t *cur = reachA, *nxt = reachB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int r = 0; r < nsrc; r++) cur[r * G] = 1ULL << r;
    for (int step = 0; step < DD; step++) {
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            const int *a = adj + (size_t)v * MAXD;
            for (int l = 0; l < Dd; l++) x |= cur[a[l]];
            nxt[v] = x;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    uint64_t full = (1ULL << nsrc) - 1ULL;
    long long raw = 0;
    for (int v = 0; v < N; v++) raw += popc64(full & ~cur[v]);
    return raw;
}

static long long full_cost(const Cfg *c, int *raw_out) {
    long long raw = bfs_raw(c->K);
    int dup = count_dups(c);
    *raw_out = (int)raw;
    return raw + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
    rebuild_all(c);
}

/* Simulated annealing; leaves *cur at the best state found. Returns its cost. */
static long long anneal(Cfg *cur, long iters, double T0, double T1) {
    int K = cur->K;
    int raw = 0;
    rebuild_all(cur);
    long long c = full_cost(cur, &raw);
    Cfg bestc = *cur;
    long long bestcost = c;
    for (long t = 0; t < iters && bestcost > 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd);
        int i = rint_(K);
        int swapmove = (K >= 2 && rint_(4) == 0);
        int i2 = i, old_s = 0;
        if (swapmove) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = cur->P[l][i];
            cur->P[l][i] = cur->P[l][i2];
            cur->P[l][i2] = tmp;
        } else {
            old_s = cur->S[l][i];
            cur->S[l][i] = rint_(GG);
        }
        rebuild_dart(cur, l);
        long long c2 = full_cost(cur, &raw);
        long long delta = c2 - c;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            c = c2;
            if (c < bestcost) {
                bestcost = c;
                bestc = *cur;
            }
        } else {
            if (swapmove) {
                int tmp = cur->P[l][i];
                cur->P[l][i] = cur->P[l][i2];
                cur->P[l][i2] = tmp;
            } else {
                cur->S[l][i] = old_s;
            }
            rebuild_dart(cur, l);
        }
    }
    *cur = bestc;
    rebuild_all(cur);
    return bestcost;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18,
                         20, 21, 24, 27, 28, 30, 32, 36, 40};

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int best_n = min_n, have = 0, fails = 0;
    Cfg best;
    memset(&best, 0, sizeof(best));
    int bM = 1, bK = 1, bR = 1;
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline) {
        int K = (rint_(100) < 60) ? 1 : ((rint_(100) < 75) ? 2 : 3);
        long long Gmin = ((long long)best_n + 2 + 2 * K - 1) / (2 * K);
        if (Gmin < 2) Gmin = 2;
        int k = KF[rint_(nk)];
        long long span = 2 + fails / 12;
        long long cap_span = Gmin / 8 + 2;
        if (span > cap_span) span = cap_span;
        long long G0 = ((Gmin + k - 1) / k) * k;
        long long G = G0 + (long long)k * rint_((int)span + 1);
        if (G > MAXG) continue;

        int m = (int)(G / k);
        int r = 1;
        if (k > 1 && m > 2 && rint_(3) != 0) {
            for (int t = 0; t < 300; t++) {
                long long c = 2 + (long long)rint_(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        set_group(m, k, r);
        int N = 2 * K * GG;
        ensure_cap(N);

        Cfg cur;
        memset(&cur, 0, sizeof(cur));
        cur.K = K;
        random_cfg(&cur);
        long long res = anneal(&cur, 120000, 2.0, 0.15);
        if (res == 0) {
            best_n = N;
            best = cur;
            bM = m;
            bK = K;
            bR = r;
            have = 1;
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = bK, G = GG, n = 2 * K * G;
    long edges_m = (long)Dd * K * G;
    printf("%d %ld\n", n, edges_m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Annealed bi-Cayley search in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
