import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Bi-Cayley lift over G = Z_m x|_r Z_k with K base vertices per side and Dd
# layers. Layer l is a permutation P[l] of the K base vertices plus one
# voltage S[l][i] per dart, so every vertex has degree Dd.
# A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, and dart (l,i) joins A_{i,g} to
# B_{P[l][i], g*S[l][i]}.
#
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly. Cost = unreached (rep, vertex) pairs plus a
# duplicate-edge penalty.
#
# Search (combined from two earlier engines):
#  - Ratchet: targets are sampled just above best_n / (2K), so every success
#    is a strict improvement over the best order found so far.
#  - Each group attempt does one fresh anneal, then up to a few reheats from
#    the attempt's best state with a random kick (progress is not thrown away).
#  - Group families Z_m x|_r Z_k: r is picked uniformly among all valid
#    multipliers (r^k = 1 mod m, gcd(r, m) = 1), not just by random sampling.
#
# Usage: prog d D seed time_limit [min_n]
# Prints the first valid graph found above min_n as "n m" plus edges, or "0 0".
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
#define MAXG 6000
#define PEN 1000
#define BIGC (1 << 30)
#define ITERS_FRESH 30000L
#define ITERS_RE 10000L
#define REHEATS 3

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
static int gpow[64];

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

/* (a,b)(c,d) = (a + r^b c, b + d), element (a,b) coded as a*K + b. */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_q = NULL;
static uint32_t *g_vis = NULL;
static uint32_t g_stamp = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_q);
    free(g_vis);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_q = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(uint32_t));
    if (!g_adj || !g_cnt || !g_q || !g_vis) {
        printf("0 0\n");
        exit(0);
    }
    g_stamp = 0;
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

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        if (g_stamp >= 0xFFFFFFF0u) {
            memset(g_vis, 0, sizeof(uint32_t) * (size_t)N);
            g_stamp = 0;
        }
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

static Cfg cur, att_best;
static int att_cost = BIGC;
static double deadline = 0.0;
static int timed_out = 0;

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

static void kick(Cfg *c) {
    int nk = c->K * Dd / 4 + 1;
    for (int q = 0; q < nk; q++) {
        int l = rint_(Dd);
        int i = rint_(c->K);
        c->S[l][i] = rint_(c->G);
    }
}

/* Anneal cur; tracks the attempt's best state in att_best / att_cost. */
static int anneal(long iters, double T0) {
    int c = cost_of(&cur);
    if (c < att_cost) {
        att_cost = c;
        att_best = cur;
    }
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.03;
        int l = rint_(Dd);
        int i = rint_(cur.K);
        if (cur.K >= 2 && rint_(4) == 0) {
            int i2 = rint_(cur.K - 1);
            if (i2 >= i) i2++;
            int tmp = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = tmp;
            int c2 = cost_of(&cur);
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                tmp = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = tmp;
            }
        } else {
            int old = cur.S[l][i];
            int ns = rint_(cur.G);
            if (ns == old) continue;
            cur.S[l][i] = ns;
            int c2 = cost_of(&cur);
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                cur.S[l][i] = old;
            }
        }
        if (c < att_cost) {
            att_cost = c;
            att_best = cur;
        }
    }
    return c;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36};
#define NKF ((int)(sizeof(KF) / sizeof(KF[0])))

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

/* Pick k from the family, m = ceil(target / k), and r uniformly among valid multipliers. */
static int sample_group(long long target, int *oM, int *oK, int *oR) {
    int k = KF[rint_(NKF)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    if (m * k > MAXG) return 0;
    int r = 1;
    if (k > 1 && m > 2) {
        int cnt = 0;
        for (long long c = 2; c < m; c++) {
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                cnt++;
                if (rint_(cnt) == 0) r = (int)c;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = r;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    Dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have_best = 0;
    Cfg best_cfg;
    int bM = 1, bK = 1, bR = 1;

    while (!timed_out && now_s() < deadline) {
        int rk = rint_(100);
        int Kc = rk < 50 ? 1 : (rk < 78 ? 2 : (rk < 90 ? 3 : (rk < 96 ? 4 : 5)));
        long long gmin = (long long)best_n / (2LL * Kc) + 1;
        long long span = gmin / 20 + 2;
        long long T = gmin + (long long)rint_((int)span);

        int gm, gk, gr;
        if (!sample_group(T, &gm, &gk, &gr)) continue;
        set_group(gm, gk, gr);
        int G = GG;
        if (G > MAXG) continue;
        int N = 2 * Kc * G;
        if (N <= best_n) continue;

        cur.K = Kc;
        cur.G = G;
        ensure_cap(N);
        random_cfg(&cur);
        att_cost = BIGC;
        int c = anneal(ITERS_FRESH, 1.5);
        int re = 0;
        while (c != 0 && !timed_out && re < REHEATS) {
            cur = att_best;
            kick(&cur);
            c = anneal(ITERS_RE, 0.6);
            re++;
        }
        if (c == 0) {
            best_n = N;
            best_cfg = cur;
            bM = gm;
            bK = gk;
            bR = gr;
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
    long nm = (long)Dd * K * G;
    printf("%d %ld\n", n, nm);
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
# Python glue: exact constructions first, then the C search from the best known order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Keep a margin for compilation, process start and parsing.
    deadline = start + max(4.0, time_limit - 8.0)

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

    # Exact constructions; calibration-style cases return immediately.
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

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic()
        if c_budget >= 3.0:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, (int(seed) % 999999937) + 1, f"{c_budget:.2f}", best_n],
                    timeout=c_budget + 6.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
