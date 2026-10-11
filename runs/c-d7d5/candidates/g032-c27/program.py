import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (cheap, always valid for the cases they cover).
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
# C engine (new construction family): simulated annealing over bi-regular
# group lifts. Base graph has K vertices per side (K up to 6), darts are
# permutations P[l] of the K-blocks with group voltages S[l][i]. The group is
# Z_m x| Z_k (semidirect, r^k = 1 mod m); k = 1 gives cyclic lifts. Cost is the
# number of (block representative, vertex) pairs at distance > DD plus a
# penalty for parallel darts. Cost 0 is a valid graph of degree Dd, bipartite,
# diameter <= DD. Left translations are automorphisms, so one BFS per block
# suffices.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 6
#define MAXNCAP 40000
#define PEN 20
#define ITERS 80000L
#define T0 6.0
#define T1 0.2

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rfloat(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static int gpow[64];
static double deadline = 0.0;

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

/* (a,b)*(c,d) = (a + r^b c, b + d), element coded as a*GK + b. */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, d = y - c * GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    int e = (b + d) % GK;
    return (int)t * GK + e;
}

static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_cap = 0, g_stamp = 0;

static void ensure_cap(int N) {
    if (N <= g_cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    g_cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static long long evalc(const Cfg *c, long long *raw_out) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) g_cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                g_adj[(size_t)a * Dd + g_cnt[a]++] = b;
                g_adj[(size_t)b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        g_stamp++;
        int head = 0, tail = 0, src = r * G;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = g_q[head++];
                const int *au = g_adj + (size_t)u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = au[t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        raw += (long long)(N - tail);
    }
    if (raw_out) *raw_out = raw;
    return raw + (long long)PEN * dup;
}

static void random_cfg(Cfg *c, int K) {
    c->K = K;
    c->G = GG;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][j];
            c->P[l][j] = t;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(GG);
    }
}

/* Simulated annealing on the full cost. Returns the best cost seen; *best holds that state. */
static long long sa_run(Cfg *c, Cfg *best) {
    long long raw = 0;
    long long cc = evalc(c, &raw);
    long long bc = cc;
    *best = *c;
    for (long t = 0; t < ITERS && bc > 0; t++) {
        if ((t & 15) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)ITERS);
        int K = c->K;
        int l = rint_(Dd), i = rint_(K);
        int kind = (K >= 2 && rint_(3) == 0);
        int i2 = 0, oldS = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            oldS = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long nc = evalc(c, &raw);
        long long delta = nc - cc;
        if (delta <= 0 || rfloat() < exp(-(double)delta / T)) {
            cc = nc;
            if (cc < bc) {
                bc = cc;
                *best = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = oldS;
            }
        }
    }
    return bc;
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

static void print_graph(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < Dd; l++)
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
        }
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
    for (int w = 0; w < 4; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;

    static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20, 21,
                             24, 28, 30, 32, 36, 40, 42, 48, 56, 60};
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));

    long long best_n = min_n;
    int have = 0;
    Cfg gbest;
    memset(&gbest, 0, sizeof(gbest));
    int bM = 1, bKk = 1, bR = 1;
    int fails = 0;

    while (now_s() < deadline) {
        int r100 = rint_(100);
        int K = r100 < 45 ? 1 : r100 < 70 ? 2 : r100 < 85 ? 3 : r100 < 93 ? 4 : r100 < 97 ? 5 : 6;

        long long G0 = best_n / (2LL * K) + 1;
        if (G0 > MAXNCAP / (2LL * K)) break;
        long long span = 2 + G0 / 50 + fails / 8;
        if (span > G0 / 4 + 3) span = G0 / 4 + 3;
        long long G = G0 + rint_((int)span + 1);
        if (G < 2) G = 2;
        if (G > MAXNCAP / (2LL * K)) G = MAXNCAP / (2LL * K);
        int Gi = (int)G;

        int k = KF[rint_(nk)];
        if (Gi % k != 0) k = 1;
        int m = Gi / k, r = 1;
        if (k > 1) {
            if (m < 3) {
                k = 1;
                m = Gi;
                r = 1;
            } else {
                int ok = 0;
                for (int t = 0; t < 300 && !ok; t++) {
                    long long c = 2 + rint_(m - 2);
                    if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                        r = (int)c;
                        ok = 1;
                    }
                }
                if (!ok) {
                    k = 1;
                    m = Gi;
                    r = 1;
                }
            }
        }
        set_group(m, k, r);

        int N = 2 * K * GG;
        ensure_cap(N);
        Cfg cur, cb;
        random_cfg(&cur, K);
        long long bc = sa_run(&cur, &cb);
        if (bc == 0) {
            long long raw = 0;
            long long chk = evalc(&cb, &raw);
            if (chk == 0) {
                best_n = N;
                gbest = cb;
                bM = m;
                bKk = k;
                bR = r;
                have = 1;
                fails = 0;
                continue;
            }
        }
        fails++;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bKk, bR);
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the C lift search seeded with the
# best valid order so far. Every return path is checked with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
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
