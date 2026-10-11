import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact / safe constructions (Python side).
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
# C search engine.
#
# Bi-Cayley lift over G = Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b) with
# K base vertices per side. Vertices A_{i,g} = i*G + g and B_{j,h} = (K+j)*G + h.
# Each of the DD... (Dd) layers is a permutation P[l] of the K base vertices with
# a voltage S[l][i] per dart, so dart (l, i) joins A_{i,g} to B_{P[l][i], g*S}.
# Every vertex has degree Dd. Left multiplication is an automorphism, so BFS
# from the 2K block representatives decides the diameter exactly.
#
# Cost = unreached (rep, vertex) pairs within DIAM steps + PEN * duplicate darts.
# Cost 0 means a valid lift.
#
# Search (merged from both parents):
#   * the engine climbs the order itself: each group attempt targets an order
#     strictly above the best found so far (ratchet), starting from the Python
#     construction's order (min_n);
#   * each group attempt runs simulated annealing with restarts: a random start,
#     then reheats from the best state of that group with a random kick;
#   * moves: change one voltage, or swap two targets within one layer.
#
# Usage: prog d D seed time_limit min_n
# Prints a valid graph ("n m" + edges) with n > min_n, or "0 0".
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
#define PEN 1000
#define MAXGG 8000
#define BIGC 1000000000
#define RL 20000

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

static double rdbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];

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
    return (int)(t * GK + (b + d) % GK);
}

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_stamp = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_stamp = 0;
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        printf("0 0\n");
        exit(0);
    }
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
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
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    if (g_stamp >= 2000000000) {
        memset(g_vis, 0, sizeof(int) * (size_t)N);
        g_stamp = 0;
    }
    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[(size_t)u * Dd + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return (int)unreached + PEN * dup;
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
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(c->G);
    }
}

static Cfg cur, gbest_cfg, best_cfg;
static int gbestc = BIGC;

/* Anneal from the current state; tracks the best state of the current group in gbest_cfg. */
static int anneal(long iters, double T0, double dl) {
    int c = cost_of(&cur);
    if (c < gbestc) {
        gbestc = c;
        gbest_cfg = cur;
    }
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 63) == 0 && now_s() > dl) break;
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.03;
        int l = rint_(Dd);
        int i = rint_(cur.K);
        int do_swap = (cur.K >= 2 && rint_(4) == 0);
        int i2 = 0, old_s = 0;
        if (do_swap) {
            i2 = rint_(cur.K - 1);
            if (i2 >= i) i2++;
            int tmp = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = tmp;
        } else {
            old_s = cur.S[l][i];
            cur.S[l][i] = rint_(cur.G);
        }
        int c2 = cost_of(&cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
            if (c < gbestc) {
                gbestc = c;
                gbest_cfg = cur;
            }
        } else {
            if (do_swap) {
                int tmp = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = tmp;
            } else {
                cur.S[l][i] = old_s;
            }
        }
    }
    return c;
}

/* Search one group until a valid lift (cost 0) is found or the deadline passes. */
static int group_search(double dl) {
    gbestc = BIGC;
    int have = 0;
    while (now_s() < dl) {
        if (!have || rdbl() < 0.25) {
            random_cfg(&cur);
            anneal(RL, 1.5, dl);
        } else {
            cur = gbest_cfg;
            int kick = cur.K * Dd / 6 + 1;
            for (int q = 0; q < kick; q++) {
                int l = rint_(Dd), i = rint_(cur.K);
                cur.S[l][i] = rint_(cur.G);
            }
            anneal(RL, 0.8, dl);
        }
        have = 1;
        if (gbestc == 0) return 1;
    }
    return gbestc == 0;
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

static const int KF[] = {1, 1, 1, 2, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14,
                         16, 18, 20, 24, 28, 30, 32, 36};

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    Dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int best_n = atoi(argv[5]);

    if (Dd < 3 || Dd > MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    double deadline = t0 + tl;
    int have_best = 0;
    int bM = 1, bK = 1, bR = 1;
    int nKF = (int)(sizeof(KF) / sizeof(KF[0]));

    while (now_s() < deadline - 0.5) {
        int rk = rint_(100);
        int Kc = rk < 50 ? 1 : (rk < 80 ? 2 : (rk < 92 ? 3 : (rk < 98 ? 4 : 5)));
        long long gmin = (long long)best_n / (2LL * Kc) + 1;
        long long span = gmin / 60 + 2;
        long long target = gmin + (long long)rint_((int)span);

        int k2 = KF[rint_(nKF)];
        long long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        if (mm * k2 > MAXGG) continue;

        int r = 1;
        if (k2 > 1 && mm > 2) {
            for (int t = 0; t < 300; t++) {
                long long c = 2 + (long long)rint_((int)(mm - 2));
                if (gcdll(c, mm) == 1 && powmod(c, k2, mm) == 1 % mm) {
                    r = (int)c;
                    break;
                }
            }
        }

        int N = 2 * Kc * (int)(mm * k2);
        if (N <= best_n) continue;

        set_group((int)mm, k2, r);
        cur.K = Kc;
        cur.G = GG;
        ensure_cap(N);

        double slice = 3.0 + 9.0 * rdbl();
        double dl = now_s() + slice;
        if (dl > deadline) dl = deadline;

        if (group_search(dl)) {
            best_cfg = gbest_cfg;
            bM = (int)mm;
            bK = k2;
            bR = r;
            best_n = N;
            have_best = 1;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK, bR);
    int K = best_cfg.K, G = best_cfg.G;
    int n = 2 * K * G;
    long edges = (long)Dd * K * G;
    printf("%d %ld\n", n, edges);
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
# Python glue: exact constructions first, then the C search above the best known order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        # Araujo-Pardo and Lopez record for D = 3, d = q + 2 with q a prime power.
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C anneals voltages of bi-Cayley lifts and climbs the order
    # from best_n upward.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.5
        if c_budget >= 1.0:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed & 0x7FFFFFFF, f"{c_budget:.2f}", best_n],
                    timeout=time_limit - 3.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
