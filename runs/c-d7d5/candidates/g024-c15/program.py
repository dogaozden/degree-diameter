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
# C engine: climbing simulated annealing over bi-Cayley graphs with K = 1.
#
# Group G (cyclic or Z_m x| Z_k), vertices A_g = g and B_h = G + h.
# Dart l joins A_g to B_{g*s_l}, with s_0..s_{Dd-1} distinct, so the graph is
# simple, Dd-regular and bipartite with 2G vertices. Left multiplication is an
# automorphism that is transitive on each side, so the diameter is at most DD
# iff BFS from A_1 and from B_1 reaches everything within DD steps.
# Cost = unreached vertices from A_1 + unreached from B_1. Cost 0 means valid.
# The search climbs: it tries group orders just above the best valid one.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 64

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
static int GM = 1, GK = 1, G = 1;
static int gpow[MAXK];
static int *inv_t = NULL, *vis = NULL, *qu = NULL;
static int capN = 0, vstamp = 0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    G = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void ensure(int N2) {
    if (N2 <= capN) return;
    free(inv_t);
    free(vis);
    free(qu);
    capN = N2;
    inv_t = malloc(sizeof(int) * (size_t)N2);
    vis = calloc((size_t)N2, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N2);
    vstamp = 0;
    if (!inv_t || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static void build_inv(void) {
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            if (gmul(x, y) == 0) {
                inv_t[x] = y;
                break;
            }
        }
    }
}

/* Number of vertices reached from src within DD steps. */
static int reach(const int *S, int src) {
    vstamp++;
    int head = 0, tail = 0;
    qu[tail++] = src;
    vis[src] = vstamp;
    for (int lvl = 0; lvl < DD; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qu[head++];
            if (u < G) {
                for (int l = 0; l < Dd; l++) {
                    int v = G + gmul(u, S[l]);
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            } else {
                int h = u - G;
                for (int l = 0; l < Dd; l++) {
                    int v = gmul(h, inv_t[S[l]]);
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

static int cost(const int *S) {
    int N2 = 2 * G;
    return (N2 - reach(S, 0)) + (N2 - reach(S, G));
}

static int anneal(int *S, double secs, double T0, double T1, int *bestS) {
    int cur = cost(S), best = cur;
    memcpy(bestS, S, sizeof(int) * (size_t)Dd);
    double t0 = now_s();
    double T = T0;
    for (long it = 0; best > 0; it++) {
        if ((it & 127) == 0) {
            double el = now_s() - t0;
            if (el >= secs) break;
            double f = el / secs;
            T = T0 * pow(T1 / T0, f);
        }
        int l = rint_(Dd);
        int old = S[l];
        int nv;
        for (;;) {
            nv = rint_(G);
            int dup = 0;
            for (int t = 0; t < Dd; t++)
                if (S[t] == nv) {
                    dup = 1;
                    break;
                }
            if (!dup) break;
        }
        S[l] = nv;
        int c2 = cost(S);
        if (c2 <= cur || urand() < exp((double)(cur - c2) / T)) {
            cur = c2;
            if (cur < best) {
                best = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)Dd);
            }
        } else {
            S[l] = old;
        }
    }
    return best;
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

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    double deadline = t0 + tl;
    int bestG = min_n / 2;      /* 2G > min_n for every G > bestG */
    int found = 0, bM = 1, bK = 1, bR = 1;
    int S[MAXD], tmpS[MAXD], bS[MAXD];

    for (;;) {
        double left = deadline - now_s();
        if (left < 0.05) break;

        int step = 2 + bestG / 40;
        int Gc = bestG + 1 + rint_(step);

        int divs[MAXK], nd = 0;
        for (int k = 1; k <= 60 && k <= Gc; k++)
            if (Gc % k == 0 && Gc / k >= 2) divs[nd++] = k;
        if (nd == 0) {
            if (Gc > bestG) bestG = Gc;
            continue;
        }

        int k = divs[rint_(nd)];
        int m = Gc / k, r = 1;
        if (k > 1) {
            int got = 0;
            if (m >= 3) {
                for (int t = 0; t < 300 && !got; t++) {
                    long long c = 2 + rint_(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                        r = (int)c;
                        got = 1;
                    }
                }
            }
            if (!got) {
                k = 1;
                m = Gc;
                r = 1;
            }
        }

        set_group(m, k, r);
        if (G < Dd) {                 /* too small for Dd distinct darts */
            if (G > bestG) bestG = G;
            continue;
        }
        ensure(2 * G);
        build_inv();

        for (int l = 0; l < Dd; l++) {
            int v;
            for (;;) {
                v = rint_(G);
                int dup = 0;
                for (int t = 0; t < l; t++)
                    if (S[t] == v) {
                        dup = 1;
                        break;
                    }
                if (!dup) break;
            }
            S[l] = v;
        }

        double att = left < 0.6 ? left : 0.6;
        int res = anneal(S, att, 2.0, 0.05, tmpS);
        if (res == 0) {
            bestG = G;
            found = 1;
            bM = m;
            bK = k;
            bR = r;
            memcpy(bS, tmpS, sizeof(int) * (size_t)Dd);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    ensure(2 * G);
    int N = 2 * G;
    printf("%d %d\n", N, Dd * G);
    for (int l = 0; l < Dd; l++) {
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", g, G + gmul(g, bS[l]));
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Group-climbing annealing in C, starting above the best known order.
    if d >= 2 and D >= 3:
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
