import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Safe exact families (fallbacks and calibration returns).
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
# C engine: bi-Cayley lifts over Z_m x|_r Z_k with K base vertices per side.
#
# Changes from the parent search (a different search dynamic):
#  * Group choice: for a sampled order T, the semidirect parameter r is drawn
#    from ALL valid units with r^k = 1 mod m (not a few random tries), and the
#    group order is an exact divisor of T when possible, so the orders scanned
#    are the exact group orders that give N = 2*K*|G|.
#  * Each group gets a fresh anneal from random, then an iterated-local-search
#    step: the best state seen is perturbed by a few random moves and annealed
#    again at lower temperature, instead of simply reheating the final state.
#  * Anneal length scales with N so large groups converge.
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins A_{i,g}
# to B_{P[l][i], g*S[l][i]}. Each layer is a permutation, so the graph is
# Dd-regular and bipartite by construction; cost counts unreached pairs from
# the 2K base sources (the group acts on the left, so identity sources suffice).
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define MAXG 4000
#define PEN 1000

typedef struct {
    int K;
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
static int GM = 1, GK = 1, GG = 1, GR = 1;
static long long gpow[64];

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    GR = r;
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
    if (!g_adj || !g_cnt || !g_vis || !g_q) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = GG, N = 2 * K * G;
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

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        g_stamp++;
        if (g_stamp == 0x7fffffff) {
            memset(g_vis, 0, sizeof(int) * (size_t)N);
            g_stamp = 1;
        }
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = g_q[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = g_adj[u * Dd + t];
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

static Cfg cur, bstate, best_cfg;
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
        for (int i = 0; i < c->K; i++) c->S[l][i] = rint_(GG);
    }
}

static void perturb(Cfg *c, int moves) {
    for (int t = 0; t < moves; t++) {
        int l = rint_(Dd), i = rint_(c->K);
        if (c->K >= 2 && rint_(4) == 0) {
            int i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            c->S[l][i] = rint_(GG);
        }
    }
}

static int anneal(long iters, double T0, int *bc_out) {
    int c = cost_of(&cur);
    bstate = cur;
    int bc = c;
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
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
            cur.S[l][i] = rint_(GG);
        }
        int c2 = cost_of(&cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
            if (c < bc) {
                bc = c;
                bstate = cur;
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
    *bc_out = bc;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36};

/* Pick a group of order >= target (exact if a sampled k divides target).
   The parameter r is drawn from all units with r^k = 1 mod m, scanned from a random start. */
static int sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    if (rint_(2) == 0) {
        for (int t = 0; t < 8; t++) {
            int kk = KF[rint_(nk)];
            if (target % kk == 0) {
                k = kk;
                break;
            }
        }
    }
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    if (m * k > MAXG) return 0;
    int r = 1;
    if (k > 1 && m > 2) {
        long long off = rint_((int)(m - 2));
        for (long long t = 0; t < m - 2; t++) {
            long long c = 2 + (off + t) % (m - 2);
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK = k;
    *oR = r;
    return 1;
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
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    best_n = min_n;

    while (!timed_out && now_s() < deadline) {
        int rk = rint_(100);
        int Kc = rk < 50 ? 1 : (rk < 80 ? 2 : (rk < 94 ? 3 : 4));

        long long gmin = (long long)best_n / (2 * Kc) + 1;
        long long span = gmin / 12 + 3;
        long long T = gmin + (long long)rint_((int)span);

        int M, Kk, R;
        if (!sample_group(T, &M, &Kk, &R)) continue;
        set_group(M, Kk, R);
        int N = 2 * Kc * GG;
        if (N <= best_n) continue;

        ensure_cap(N);
        cur.K = Kc;
        random_cfg(&cur);

        long iters = 2000 + 4L * N;
        if (iters > 20000) iters = 20000;

        int bc1 = 0, bc2 = 0;
        int c = anneal(iters, 1.2, &bc1);
        /* Iterated local search: perturb the best state seen and re-anneal cooler. */
        if (c != 0 && !timed_out) {
            cur = bstate;
            perturb(&cur, 2 + rint_(3));
            c = anneal(iters / 2, 0.5, &bc2);
        }
        if (c == 0 && N > best_n) {
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
    int K = best_cfg.K, G = GG;
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
# Python glue: exact constructions first, then the C search seeded by the best order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Keep a margin for compilation, process start-up, parsing and validation.
    hard_end = start + max(4.0, time_limit - 8.0)

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

        # Araujo-Pardo & Lopez construction (diameter 3, valid for any D >= 3).
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4 and time.monotonic() < hard_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = hard_end - time.monotonic()
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
