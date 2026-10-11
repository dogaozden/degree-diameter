import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent).
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
# New engine (replaces the parent's breakout and edge-splitting engines):
# simulated annealing over semidirect-product bi-lifts with K base vertices
# per side. Each layer is a perfect matching between left base i and right
# base P[l][i] with voltage S[l][i] in the group. Cost = number of
# (representative, vertex) pairs at distance > DD, plus a duplicate-edge
# penalty. The group acts on each side transitively, so BFS from one
# representative per base vertex decides diameter for the whole lift.
# Moves: swap two entries of one permutation layer, or change one voltage.
# Restarts draw a fresh base size K and group until a valid lift larger
# than the current best is found.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 8
#define MAXD 16
#define MAXGG 3000
#define PEN 2
#define ITERS 15000

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

static int K = 1, G = 2, GM = 1, GK = 1;
static int gpow[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];

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

/* Semidirect product Z_m x|_r Z_k, element (a, b) coded as a*k + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int vstamp = 0;

static long long evalcost(void) {
    int N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        vstamp++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = vstamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    return raw + (long long)PEN * dup;
}

static void random_cfg(void) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(G);
    }
}

/* Anneal the current K and group. Returns 1 if a cost-0 lift is reached. */
static int anneal(long iters, double T0, double T1) {
    random_cfg();
    long long cur = evalcost();
    for (long t = 0; t < iters && cur != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(Dd), i = rint_(K);
        int swapk = (K >= 2 && rint_(3) == 0);
        int i2 = 0, olds = 0, tmp;
        if (swapk) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            olds = S[l][i];
            S[l][i] = rint_(G);
        }
        long long nc = evalcost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            if (swapk) {
                tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = olds;
            }
        }
    }
    return cur == 0;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24};

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

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
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
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    int cap = 2 * MAXK * MAXGG;
    adj = malloc(sizeof(int) * (size_t)cap * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)cap);
    vis = calloc((size_t)cap, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)cap);
    if (!adj || !cnt || !vis || !qu) {
        printf("0 0\n");
        return 0;
    }

    deadline = now_s() + tl;
    int best_n = min_n, have = 0;
    static int bP[MAXD][MAXK], bS[MAXD][MAXK];
    int bK = 1, bm = 2, bk = 1, br = 1;
    int nkf = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline) {
        int Kc = 1 + rint_(MAXK);
        long long g0 = (long long)best_n / (2 * Kc) + 1;
        long long span = g0 / 20 + 4;
        long long g = g0 + (long long)rint_((int)span);

        int kk = KF[rint_(nkf)];
        long long m = (g + kk - 1) / kk;
        if (m < 2) m = 2;
        int r = 1;
        if (kk > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)rint_((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, kk, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        if (m * kk > MAXGG) continue;
        set_group((int)m, kk, r);
        K = Kc;
        int N = 2 * K * G;
        if (N <= best_n) continue;

        if (anneal(ITERS, 3.0, 0.15)) {
            best_n = N;
            memcpy(bP, P, sizeof(P));
            memcpy(bS, S, sizeof(S));
            bK = K;
            bm = (int)m;
            bk = kk;
            br = r;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bm, bk, br);
    K = bK;
    int n = 2 * K * G;
    printf("%d %d\n", n, Dd * K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = bP[l][i], s = bS[l][i];
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
    budget = max(2.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    if d < 3 or D < 3:
        return best

    # Main search: annealed semidirect bi-lifts with varying base size.
    remaining = deadline - time.monotonic()
    if remaining >= 2.0:
        try:
            out = lib.run_c(SA_SOURCE, [d, D, seed, f"{remaining - 1.5:.2f}", best[0]],
                            timeout=remaining + 5.0)
            n3, e3 = lib.parse_graph_text(out)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
