import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (always valid, used as the floor).
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
# C engine: simulated annealing over Haar graphs of finite groups.
#
# Group G = Z_m x|_r Z_k (element a*k+b, (a,b)(c,e) = (a + r^b c, b + e)).
# Graph: A_x ~ B_{x s} for s in S, |S| = DEG, S a set of distinct elements.
# Left translations are automorphisms acting regularly on each side, so the
# diameter is <= DIAM iff BFS from A_e and from B_e reach everything within
# DIAM steps. Cost = number of unreached vertices from those two sources.
# Cost 0 is a valid graph of order 2|G|. The group order is climbed upward
# from the known lower bound, each success raising the target.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rfloat(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
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

static int DEG = 3, DIAM = 3;
static double deadline = 0.0;

static int GM = 1, GK = 1, GN = 1;
static int gpow[64];
static int *ginv = NULL;
static int cap_n = 0;
static int *vis = NULL, *qu = NULL;
static int stamp = 0;
static int *S = NULL;
static char *inS = NULL;

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int ginvf(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    long long t = (-(long long)gpow[nb] * (long long)a) % GM;
    if (t < 0) t += GM;
    return (int)t * GK + nb;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    if (cap_n < GN) {
        free(ginv);
        free(vis);
        free(qu);
        free(inS);
        cap_n = GN;
        ginv = malloc(sizeof(int) * (size_t)GN);
        vis = calloc((size_t)2 * GN, sizeof(int));
        qu = malloc(sizeof(int) * (size_t)2 * GN);
        inS = malloc((size_t)GN);
        if (!ginv || !vis || !qu || !inS) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
    }
    for (int x = 0; x < GN; x++) ginv[x] = ginvf(x);
}

/* Number of vertices reached from a source within DIAM steps.
   A vertex u < GN is on side A; GN + y is on side B. */
static int reach_count(int side, int src) {
    stamp++;
    int head = 0, tail = 0;
    int s0 = side ? GN + src : src;
    vis[s0] = stamp;
    qu[tail++] = s0;
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int end = tail;
        if (head == end) break;
        while (head < end) {
            int u = qu[head++];
            if (u < GN) {
                for (int t = 0; t < DEG; t++) {
                    int w = GN + gmul(u, S[t]);
                    if (vis[w] != stamp) {
                        vis[w] = stamp;
                        qu[tail++] = w;
                    }
                }
            } else {
                int y = u - GN;
                for (int t = 0; t < DEG; t++) {
                    int w = gmul(y, ginv[S[t]]);
                    if (vis[w] != stamp) {
                        vis[w] = stamp;
                        qu[tail++] = w;
                    }
                }
            }
        }
    }
    return tail;
}

static int cost_cur(void) {
    int t1 = reach_count(0, 0);
    int t2 = reach_count(1, 0);
    return (2 * GN - t1) + (2 * GN - t2);
}

static void random_S(void) {
    memset(inS, 0, (size_t)GN);
    for (int t = 0; t < DEG; t++) {
        int v;
        do {
            v = rint_(GN);
        } while (inS[v]);
        inS[v] = 1;
        S[t] = v;
    }
}

/* Simulated annealing on the connection set S. Returns the final cost,
   which is 0 exactly when S gives a valid graph (S is left in that state). */
static int anneal(long long steps) {
    int cur = cost_cur();
    for (long long st = 0; st < steps && cur > 0; st++) {
        if ((st & 255) == 0 && now_s() > deadline) break;
        double frac = (double)st / (double)steps;
        double T = 1.2 * pow(0.03 / 1.2, frac);
        int t = rint_(DEG);
        int old = S[t];
        int nv;
        do {
            nv = rint_(GN);
        } while (inS[nv]);
        inS[old] = 0;
        inS[nv] = 1;
        S[t] = nv;
        int c2 = cost_cur();
        if (c2 <= cur || rfloat() < exp((double)(cur - c2) / T)) {
            cur = c2;
        } else {
            inS[nv] = 0;
            inS[old] = 1;
            S[t] = old;
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    DEG = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (DEG < 2 || DEG > 40 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = now_s() + tl;
    S = malloc(sizeof(int) * (size_t)DEG);
    int *bestS = malloc(sizeof(int) * (size_t)DEG);
    if (!S || !bestS) {
        printf("0 0\n");
        return 0;
    }

    /* A graph with 2G vertices beats min_n iff G > min_n / 2. */
    int best_half = min_n / 2;
    if (best_half < DEG) best_half = DEG;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    long long fails = 0;

    while (now_s() < deadline) {
        long long span = 3 + (fails / 8 > 60 ? 60 : fails / 8);
        long long g = (long long)best_half + 1 + rint_((int)span);

        int divs[64];
        int nd = 0;
        for (int k = 1; k <= 40 && (long long)k <= g; k++) {
            if (g % k == 0 && g / k >= 2) divs[nd++] = k;
        }
        if (nd == 0) {
            fails++;
            continue;
        }
        int k = divs[rint_(nd)];
        int m = (int)(g / k);
        int r = 1;
        if (k > 1) {
            int found = 0;
            for (int t = 0; t < 200; t++) {
                int c = 1 + rint_(m - 1);
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = c;
                    found = 1;
                    break;
                }
            }
            if (!found) {
                fails++;
                continue;
            }
        }

        set_group(m, k, r);
        random_S();
        int res = anneal(25000);
        if (res == 0) {
            best_half = GN;
            have = 1;
            bM = m;
            bK = k;
            bR = r;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
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
    int n = 2 * GN;
    long mtot = (long)DEG * GN;
    printf("%d %ld\n", n, mtot);
    for (int t = 0; t < DEG; t++) {
        for (int x = 0; x < GN; x++) {
            printf("%d %d\n", x, GN + gmul(x, bestS[t]));
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the annealing search in C.
# Every candidate is checked with lib.is_valid before it can replace the best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(4.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 2.5)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
