import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (safe baselines).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 (diameter 3), when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# C engine: simulated annealing over Cayley-type bipartite graphs.
#
# Graph model (K = 1 bi-Cayley over a group G = Z_m x|_r Z_k, element a*k+b):
# vertices (g,0) = g and (h,1) = G + h. Edges (g,0)-(g*s,1) for s in S, where
# S is a set of Dd distinct group elements. Left translations are automorphisms
# that preserve both sides, so diameter <= DD holds iff BFS from (e,0) and (e,1)
# reaches every vertex within DD steps. Cost = unreached vertices from those two
# sources; cost 0 is a valid graph.
#
# Search: for each sampled group (order just above the best known n / 2),
# anneal the Dd-element connection set with single-element replacement moves.
# When a group succeeds, the window moves up to search for a larger order.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXG 2600
#define ITERS 30000

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

static int Dd = 3, DD = 3;
static double deadline = 0.0;

static int GM = 1, GK = 1, G = 1;
static int gpow[64];
static int *MT = NULL;
static int *INV = NULL;

static int gmul_calc(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    free(MT);
    free(INV);
    MT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    if (!MT || !INV) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MT[x * G + y] = gmul_calc(x, y);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) {
                INV[x] = y;
                break;
            }
}

static int adjv[2 * MAXG * MAXD];
static int visv[2 * MAXG];
static int qu[2 * MAXG];
static int stampv = 0;
static int S_inv[MAXD];

/* Number of vertices not reached within DD steps from (e,0) and (e,1), summed. */
static long long cost_S(const int *S) {
    int N = 2 * G;
    for (int t = 0; t < Dd; t++) S_inv[t] = INV[S[t]];
    for (int g = 0; g < G; g++)
        for (int t = 0; t < Dd; t++)
            adjv[g * Dd + t] = G + MT[g * G + S[t]];
    for (int h = 0; h < G; h++)
        for (int t = 0; t < Dd; t++)
            adjv[(G + h) * Dd + t] = MT[h * G + S_inv[t]];
    long long total = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? G : 0;
        stampv++;
        int head = 0, tail = 0;
        visv[src] = stampv;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adjv[u * Dd + t];
                    if (visv[v] != stampv) {
                        visv[v] = stampv;
                        qu[tail++] = v;
                    }
                }
            }
        }
        total += (long long)(N - tail);
    }
    return total;
}

/* Simulated annealing on the connection set. Returns the best cost; bestS holds its set. */
static long long anneal(int *S, int *bestS, long long iters) {
    for (int t = 0; t < Dd; t++) {
        int x, dup;
        do {
            x = rint_(G);
            dup = 0;
            for (int u = 0; u < t; u++)
                if (S[u] == x) dup = 1;
        } while (dup);
        S[t] = x;
    }
    long long c = cost_S(S), bestc = c;
    memcpy(bestS, S, sizeof(int) * (size_t)Dd);
    const double T0 = 2.0, T1 = 0.15;
    for (long long it = 0; it < iters && bestc > 0; it++) {
        if ((it & 511) == 0 && now_s() > deadline) break;
        int i = rint_(Dd);
        int x = rint_(G);
        int dup = 0;
        for (int t = 0; t < Dd; t++)
            if (S[t] == x) {
                dup = 1;
                break;
            }
        if (dup) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int old = S[i];
        S[i] = x;
        long long c2 = cost_S(S);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c < bestc) {
                bestc = c;
                memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            }
        } else {
            S[i] = old;
        }
    }
    return bestc;
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
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    long long best_n = min_n;
    int have = 0, bM = 1, bK = 1, bR = 1;
    int bestS[MAXD], Scur[MAXD], Sb[MAXD];
    long long fails = 0;
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline) {
        long long g0 = best_n / 2 + 1;
        if (g0 > MAXG / 2) break;
        long long span = g0 / 40 + 4 + fails / 8;
        if (span > g0 / 10 + 4) span = g0 / 10 + 4;
        int k = KF[rint_(nk)];
        long long target = g0 + (long long)rint_((int)span);
        long long m = (target + k - 1) / k;
        if (m < 2) m = 2;
        if (m * k > MAXG) {
            fails++;
            continue;
        }
        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)rint_((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        set_group((int)m, k, r);
        if (Dd > G || 2LL * G <= best_n) {
            fails++;
            continue;
        }
        long long c = anneal(Scur, Sb, ITERS);
        if (c == 0) {
            best_n = 2LL * G;
            have = 1;
            bM = (int)m;
            bK = k;
            bR = r;
            memcpy(bestS, Sb, sizeof(int) * (size_t)Dd);
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
    int n = 2 * G;
    printf("%d %ld\n", n, (long)Dd * G);
    for (int g = 0; g < G; g++)
        for (int t = 0; t < Dd; t++)
            printf("%d %d\n", g, G + MT[g * G + bestS[t]]);
    return 0;
}
'''

# Known good orders to start the C search above (lower bounds on n for the search).
FLOOR_N = {(7, 5): 1000}


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def attempt(fn):
        try:
            g = fn()
            if g is not None:
                consider(g[0], g[1])
        except Exception:
            pass

    if D >= 3:
        attempt(lambda: _best_pg(d))
        attempt(lambda: _araujo(d))
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < deadline:
        attempt(lambda: _best_gq(d))
        if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
            return best

    # Annealing search over Cayley-type bipartite graphs in C.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            min_n = max(best_n, FLOOR_N.get((d, D), 0))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", min_n],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
