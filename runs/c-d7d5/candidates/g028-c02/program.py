import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q) for the largest prime power q
# with q + 1 <= d. Diameter 3, so it is valid for every D >= 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# C engine: bi-Cayley search by simulated annealing.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, with G = |Z_m x|_r Z_k|.
# Dart (l, i) joins A_{i,g} to B_{P[l][i], g*S[l][i]}. Every vertex then has
# degree exactly Dd, since each P[l] is a permutation of the K classes.
#
# Cost = unreached (source, vertex) pairs within DD steps + PEN * duplicate
# darts. Left translation by the group is an automorphism that is transitive
# on each class, so one BFS source per class decides the diameter. Cost 0
# means a valid graph.
#
# Differs from the breakout search: groups are chosen as exact divisors of the
# target order, and each group gets one annealing run with a geometric cooling
# schedule. Only the best state of each run is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDART 64
#define MAXKC 2
#define MAXG 4000
#define MAXN (2 * MAXKC * MAXG)
#define PEN 3
#define ITERS 40000

typedef struct {
    int P[MAXDART][MAXKC];
    int S[MAXDART][MAXKC];
} Cfg;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 7, DD = 5;
static int K = 1, G = 1;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[256];
static double deadline = 0.0;

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = p;
        p = (p * r) % m;
    }
}

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int adj[MAXN * MAXDART];
static int vis[MAXN];
static int qu[MAXN];
static int stamp_ctr = 0;
static int g_raw = 0, g_dup = 0;

static long long eval(const Cfg *c) {
    int N = 2 * K * G;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + l] = b;
                adj[b * Dd + l] = a;
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
        stamp_ctr++;
        int head = 0, tail = 0;
        int src = r * G;
        vis[src] = stamp_ctr;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                const int *au = adj + u * Dd;
                for (int t = 0; t < Dd; t++) {
                    int v = au[t];
                    if (vis[v] != stamp_ctr) {
                        vis[v] = stamp_ctr;
                        qu[tail++] = v;
                    }
                }
            }
        }
        raw += N - tail;
    }
    g_raw = (int)raw;
    g_dup = dup;
    return raw + (long long)PEN * dup;
}

static void random_cfg(Cfg *c) {
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) c->P[l][i] = i;
        if (K == 2 && rint_(2)) {
            c->P[l][0] = 1;
            c->P[l][1] = 0;
        }
        for (int i = 0; i < K; i++) c->S[l][i] = rint_(GG);
    }
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

/* Find Z_m x|_r Z_k with m*k == Gt, using a random divisor k <= 64. */
static int pick_group(long long Gt, int *om, int *ok, int *orr) {
    int cand[64];
    int nc = 0;
    for (int k = 1; k <= 64; k++)
        if (Gt % k == 0 && Gt / k >= 3) cand[nc++] = k;
    if (nc == 0) return 0;
    for (int t = 0; t < 60; t++) {
        int k = cand[rint_(nc)];
        long long m = Gt / k;
        if (k == 1) {
            *om = (int)m;
            *ok = 1;
            *orr = 1;
            return 1;
        }
        for (int u = 0; u < 300; u++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                *om = (int)m;
                *ok = k;
                *orr = (int)c;
                return 1;
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXDART || DD < 1) {
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
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    int bK = 1, bG = 1, bm = 1, bk = 1, br = 1;
    int fails = 0;
    Cfg cur, bc;
    memset(&cur, 0, sizeof(cur));
    memset(&bc, 0, sizeof(bc));

    while (now_s() < deadline) {
        K = (rint_(100) < 70) ? 1 : 2;
        long long g0 = best_n / (2LL * K) + 1;
        if (g0 > MAXG) break;
        long long span = 2 + fails / 6;
        long long cap = g0 / 25 + 2;
        if (span > cap) span = cap;
        long long Gt = g0 + rint_((int)span + 1);
        if (Gt > MAXG) Gt = MAXG;

        int m, k, r;
        if (!pick_group(Gt, &m, &k, &r)) {
            fails++;
            continue;
        }
        set_group(m, k, r);
        G = GG;

        random_cfg(&cur);
        long long cc = eval(&cur);
        bc = cur;
        long long bcc = cc;

        for (long it = 0; it < ITERS && bcc != 0; it++) {
            if ((it & 255) == 0 && now_s() > deadline) break;
            double T = 4.0 * pow(0.05 / 4.0, (double)it / (double)ITERS);
            int l = rint_(Dd);
            int kind = (K == 2 && rint_(3) == 0);
            int li = 0, old = 0;
            if (kind) {
                int tmp = cur.P[l][0];
                cur.P[l][0] = cur.P[l][1];
                cur.P[l][1] = tmp;
            } else {
                li = rint_(K);
                old = cur.S[l][li];
                cur.S[l][li] = rint_(GG);
            }
            long long nc = eval(&cur);
            if (nc <= cc || rdbl() < exp(-(double)(nc - cc) / T)) {
                cc = nc;
                if (cc < bcc) {
                    bcc = cc;
                    bc = cur;
                }
            } else {
                if (kind) {
                    int tmp = cur.P[l][0];
                    cur.P[l][0] = cur.P[l][1];
                    cur.P[l][1] = tmp;
                } else {
                    cur.S[l][li] = old;
                }
            }
        }

        if (bcc == 0) {
            best_n = 2LL * K * G;
            best_cfg = bc;
            bK = K;
            bG = G;
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
    K = bK;
    G = bG;
    set_group(bm, bk, br);
    long long n = 2LL * K * G;
    long long me = (long long)Dd * K * G;
    printf("%lld %lld\n", n, me);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions and a valid fallback first, then the C search.
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

    # Annealing over bi-Cayley graphs, seeded with the best order so far as a
    # lower bound. The C program only prints graphs larger than that bound.
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
