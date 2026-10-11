import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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
# C engine: simulated annealing over bi-Cayley graphs on semidirect products
# Z_m x|_r Z_k (one orbit per side). Cost is the number of unreached pairs
# seen from the two base vertices (vertex-transitivity makes this exact),
# plus a penalty for repeated connection elements. The group order window
# is pushed just above the best order found so far.
#
# Vertices: A_g = g, B_h = G + h. Dart l joins A_g to B_{g*S[l]}.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXG 1700
#define PEN 40

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static double deadline = 0.0;
static int G = 1;
static int MT[MAXG * MAXG];
static int GINV[MAXG];
static int vis[2 * MAXG];
static int qu[2 * MAXG];
static int stamp_ = 0;
static int S[MAXD];

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

/* Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b. */
static void setup_group(int m, int k, int r) {
    G = m * k;
    long long gp[64];
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gp[b] = p;
        p = (p * r) % m;
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            long long t = ((long long)a + gp[b] * (long long)c) % m;
            MT[x * G + y] = (int)(t * k + (b + d) % k);
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) {
                GINV[x] = y;
                break;
            }
}

static int bfs_count(int src) {
    int head = 0, tail = 0;
    stamp_++;
    vis[src] = stamp_;
    qu[tail++] = src;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qu[head++];
            if (u < G) {
                for (int l = 0; l < Dd; l++) {
                    int v = G + MT[u * G + S[l]];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qu[tail++] = v;
                    }
                }
            } else {
                int h = u - G;
                for (int l = 0; l < Dd; l++) {
                    int v = MT[h * G + GINV[S[l]]];
                    if (vis[v] != stamp_) {
                        vis[v] = stamp_;
                        qu[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

static long long cost_S(void) {
    int dup = 0;
    for (int l = 0; l < Dd; l++)
        for (int l2 = l + 1; l2 < Dd; l2++)
            if (S[l] == S[l2]) dup++;
    int N = 2 * G;
    int ra = bfs_count(0);
    int rb = bfs_count(G);
    return (long long)(2 * N - ra - rb) + (long long)PEN * dup;
}

/* Simulated annealing on the connection set of the current group.
   Leaves the best state found in S and returns its cost. */
static long long anneal(long iters) {
    for (int l = 0; l < Dd; l++) S[l] = rint_(G);
    long long cur = cost_S();
    long long best = cur;
    int bestS[MAXD];
    memcpy(bestS, S, sizeof(int) * (size_t)Dd);
    const double T0 = 2.0, T1 = 0.05;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(Dd);
        int old = S[l];
        S[l] = rint_(G);
        long long c2 = cost_S();
        long long delta = c2 - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            }
        } else {
            S[l] = old;
        }
    }
    memcpy(S, bestS, sizeof(int) * (size_t)Dd);
    return best;
}

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
    int have = 0;
    int bGM = 1, bGK = 1, bGR = 1, bG = 1;
    int bestS[MAXD];
    int fails = 0;
    const long iters = 30000;

    while (now_s() < deadline) {
        long long lo = best_n / 2 + 1;   /* need 2G > best_n */
        if (lo < 4) lo = 4;
        long long span = 4 + fails / 10;
        if (span > 80) span = 80;
        long long Gt = lo + (long long)rint_((int)span);
        if (Gt > MAXG / 2) {
            /* Window exhausted: fall back to the top of the allowed range. */
            Gt = MAXG / 2 - (long long)rint_(40);
            if (Gt < 4) break;
        }

        int dv[64];
        int nd = 0;
        for (int k = 1; k <= 64 && k <= Gt / 2; k++)
            if (Gt % k == 0) dv[nd++] = k;
        if (nd == 0) continue;
        int k = dv[rint_(nd)];
        int m = (int)(Gt / k);
        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 500; t++) {
                long long c = 2 + (long long)rint_(m - 2);
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }

        setup_group(m, k, r);
        long long bst = anneal(iters);
        if (bst == 0) {
            best_n = 2LL * G;
            have = 1;
            bGM = m;
            bGK = k;
            bGR = r;
            bG = G;
            memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            fails = 0;
        } else {
            fails++;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bGM, bGK, bGR);
    memcpy(S, bestS, sizeof(int) * (size_t)Dd);
    int n = 2 * bG;
    long m_edges = (long)Dd * bG;
    printf("%d %ld\n", n, m_edges);
    for (int l = 0; l < Dd; l++) {
        for (int g = 0; g < bG; g++) {
            printf("%d %d\n", g, bG + MT[g * bG + S[l]]);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        # Araujo-Pardo & Lopez graph: degree q+2 = d, diameter 3 (valid for D >= 3).
        if d >= 5 and lib.is_prime_power(d - 2) and time.monotonic() < deadline:
            try:
                al = lib.araujo_lopez_graph(d - 2)
                consider(al[0], al[1])
            except Exception:
                pass
            if D == 3:
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley annealing over semidirect products, seeded with the best order so far.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
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
