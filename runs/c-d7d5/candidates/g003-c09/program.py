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
# Bolder search engine in C: bi-Cayley / multi-base lifts over Z_m x|_r Z_k.
#
# Changes from the previous engine:
#   * Cost is a weighted count of unreached (rep, vertex) pairs beyond DD, plus a
#     duplicate-dart penalty; ties are broken by a small secondary term (sum of
#     distances of far vertices) so annealing sees a gradient.
#   * Semidirect parameters r are searched exhaustively for small m, not sampled.
#   * Annealing uses reheating rounds: a stalled run is restarted from its best
#     configuration rather than from scratch.
#   * Base-vertex count K goes up to 6, with more weight on K = 2..4 for
#     degree-7 targets.
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
#define PEN 100000
#define ITERS 12000
#define ROUNDS 4

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

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int GM = 1, GK = 1, GG = 1;
static long long gpow[64];

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d). */
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

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL, *g_lvl = NULL;
static int g_stamp = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    free(g_lvl);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_lvl = malloc(sizeof(int) * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q || !g_lvl) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

/* Cost: unreached pairs within reach DD (weight 1000 each) plus a
   tie-breaking term: sum over reached-but-late vertices of their excess distance,
   plus PEN per duplicate dart. Zero iff the lift is valid. */
static long long cost_of(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                g_adj[a * Dd + g_cnt[a]++] = b;
                g_adj[b * Dd + g_cnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long unreached = 0, excess = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_lvl[src] = 0;
        g_q[tail++] = src;
        int lvl = 0;
        while (head < tail && lvl < 4 * DD) {
            int end = tail;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
                    if (g_vis[v] != g_stamp) {
                        g_vis[v] = g_stamp;
                        g_lvl[v] = lvl + 1;
                        g_q[tail++] = v;
                    }
                }
            }
            lvl++;
        }
        /* vertices reached beyond DD contribute excess; unreached contribute fixed penalty */
        for (int t = 0; t < tail; t++) {
            int v = g_q[t];
            if (g_lvl[v] > DD) excess += g_lvl[v] - DD;
        }
        unreached += N - tail;
    }
    return 1000LL * unreached + excess + (long long)PEN * dup;
}

static Cfg cur, best_cfg, run_best;
static int have_best = 0, best_n = 0;
static int bM = 1, bK = 1, bR = 1;
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

static long long anneal(long iters, double T0, Cfg *out_best) {
    long long c = cost_of(&cur);
    long long bc = c;
    *out_best = cur;
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.05;
        int l = rint_(Dd);
        int i = rint_(cur.K);
        int swap_kind = (cur.K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (swap_kind) {
            i2 = rint_(cur.K - 1);
            if (i2 >= i) i2++;
            int tmp = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = tmp;
        } else {
            old_s = cur.S[l][i];
            cur.S[l][i] = rint_(cur.G);
        }
        long long c2 = cost_of(&cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / (temp * 1000.0))) {
            c = c2;
            if (c < bc) {
                bc = c;
                *out_best = cur;
            }
        } else {
            if (swap_kind) {
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36};

/* Pick a group of order about target: k from KF, m = ceil(target/k), r exhaustive for small m. */
static int pick_r(long long m, int k) {
    if (k == 1 || m <= 2) return 1;
    int cands[4096];
    int nc = 0;
    if (m <= 4096) {
        for (long long c = 2; c < m && nc < 4096; c++) {
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) cands[nc++] = (int)c;
        }
    } else {
        for (int t = 0; t < 2000 && nc < 4096; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) cands[nc++] = (int)c;
        }
    }
    if (nc == 0) return 1;
    return cands[rint_(nc)];
}

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = pick_r(m, k);
    *oM = (int)m;
    *oK = k;
    *oR = r;
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
    deadline = t0 + tl;
    best_n = min_n;

    while (!timed_out && now_s() < deadline) {
        /* K distribution: favour 1..4 (Cayley and small multi-base lifts). */
        int rk = rint_(100);
        int Kc = rk < 35 ? 1 : (rk < 60 ? 2 : (rk < 80 ? 3 : (rk < 93 ? 4 : (rk < 98 ? 5 : 6))));

        long long gmin = (long long)best_n / (2 * Kc) + 1;
        long long span = gmin / 30 + 2;
        long long target = gmin + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 8000 || Kc > MAXK) continue;
        int N = 2 * Kc * GG;
        if (N <= best_n) continue;

        ensure_cap(N);
        cur.K = Kc;
        cur.G = GG;
        random_cfg(&cur);

        int found = 0;
        for (int round = 0; round < ROUNDS && !found && !timed_out; round++) {
            double T0 = 1.5 - 0.3 * round;
            Cfg rb;
            long long c = anneal(ITERS, T0, &rb);
            if (c == 0) {
                found = 1;
                best_cfg = cur;
                break;
            }
            /* Reheat from the best configuration of this round. */
            cur = rb;
        }
        if (found && N > best_n) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bK = Kk;
            bR = R;
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
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
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
    deadline = start + max(4.0, min(0.85 * time_limit, time_limit - 6.0))

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

    # Exact constructions: return immediately for calibration-style cases.
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
        c_budget = deadline - time.monotonic() - 2.0
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
