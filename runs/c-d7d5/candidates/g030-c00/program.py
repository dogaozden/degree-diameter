import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions.
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
# C engine: bi-Cayley simulated annealing over semidirect-product groups.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}, where P[l] is a permutation of 0..K-1
# (so every B vertex has degree Dd). Cost = unreached (source, vertex) pairs
# from one representative per side within DD steps + PEN * duplicate darts.
# Cost 0 means a valid graph. Moves: resample one connection value, or swap
# two entries of a permutation. Groups Z_m x| Z_k are sampled freshly for each
# restart, with the order window moving above the best order found so far.
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
#define MAXG 1200
#define MAXN (2 * MAXK * MAXG)
#define PEN 40

typedef struct {
    int K, G;
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

static int ri(int n) { return (int)(rnd() % (uint64_t)n); }

static double rf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 5;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static int gm[MAXG * MAXG];
static double deadline = 0.0;

static int adj[MAXN * MAXD];
static int cnt[MAXN], vis[MAXN], qu[MAXN];
static int stamp = 0;

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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void build_table(void) {
    for (int x = 0; x < GG; x++)
        for (int y = 0; y < GG; y++)
            gm[x * GG + y] = gmul(x, y);
}

/* Weighted-free cost: unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts. */
static long long eval_cfg(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gm[g * G + s];
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stamp++;
        int h = 0, t = 0;
        vis[src] = stamp;
        qu[t++] = src;
        for (int lv = 0; lv < DD && h < t; lv++) {
            int end = t;
            while (h < end) {
                int u = qu[h++];
                for (int q = 0; q < Dd; q++) {
                    int v = adj[u * Dd + q];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[t++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - t);
    }
    return raw + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < c->K; i++) c->P[l][i] = i;
        for (int i = c->K - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < c->K; i++) c->S[l][i] = ri(GG);
    }
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18,
                         20, 21, 24, 27, 28, 30, 32, 36, 40, 42, 45, 48, 50, 54, 56, 60};
static const int NKF = (int)(sizeof(KF) / sizeof(KF[0]));

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

static int sample_group(long long Gt, int *om, int *ok, int *orr) {
    for (int tries = 0; tries < 60; tries++) {
        int k = KF[ri(NKF)];
        long long m = (Gt + k - 1) / k;
        if (m < 2) m = 2;
        if (m * k > MAXG) continue;
        int r = 1;
        if (k > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                long long c = 2 + (long long)ri((int)(m - 2));
                if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                    r = (int)c;
                    break;
                }
            }
        }
        *om = (int)m;
        *ok = k;
        *orr = r;
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    int bm = 1, bk = 1, br = 1;
    Cfg best;
    memset(&best, 0, sizeof(best));
    long long fails = 0;

    while (now_s() < deadline) {
        int K = ri(100) < 65 ? 1 : (ri(100) < 60 ? 2 : 3);
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 30 + 4 + fails / 25;
        if (span > g0 / 4 + 4) span = g0 / 4 + 4;
        long long Gt = g0 + ri((int)span + 1);

        int m, k, r;
        if (!sample_group(Gt, &m, &k, &r)) continue;
        set_group(m, k, r);
        int G = GG;
        int N = 2 * K * G;
        if (N <= best_n || N > MAXN) continue;
        build_table();

        Cfg cur;
        cur.K = K;
        cur.G = G;
        random_cfg(&cur);
        long long cost = eval_cfg(&cur);
        Cfg bc = cur;
        long long bcost = cost;

        long iters = 40000;
        for (long it = 0; it < iters && bcost > 0; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = 3.0 * (1.0 - (double)it / (double)iters) + 0.05;
            int l = ri(Dd), i = ri(K);
            Cfg nw = cur;
            if (K >= 2 && ri(4) == 0) {
                int i2 = ri(K - 1);
                if (i2 >= i) i2++;
                int tmp = nw.P[l][i];
                nw.P[l][i] = nw.P[l][i2];
                nw.P[l][i2] = tmp;
            } else {
                nw.S[l][i] = ri(G);
            }
            long long nc = eval_cfg(&nw);
            long long dl = nc - cost;
            if (dl <= 0 || rf() < exp(-(double)dl / T)) {
                cur = nw;
                cost = nc;
                if (cost < bcost) {
                    bcost = cost;
                    bc = cur;
                }
            }
        }

        if (bcost == 0) {
            best_n = N;
            best = bc;
            bm = m;
            bk = k;
            br = r;
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
    set_group(bm, bk, br);
    build_table();
    int K = best.K, G = best.G;
    int N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gm[g * G + s]);
            }
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Simulated annealing over bi-Cayley lifts, seeded with the best known order.
    if d >= 3 and D >= 3:
        tl = float(time_limit)
        budget = min(0.85 * tl, tl - 7.0) - (time.monotonic() - start) - 1.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=tl - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
