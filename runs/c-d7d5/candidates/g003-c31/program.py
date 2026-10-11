import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and semi-exact baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph of degree d = q + 2 (diameter 3), when d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
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
# New engine: bi-Cayley voltage lifts over a broad family of groups
# Z_m x|_r Z_k (r = 1 gives the direct product). Each block has K base vertices
# per side, and each of the Dd layers is a permutation of the K sides plus one
# group voltage per dart. Left multiplication is an automorphism, so BFS from
# the 2K block representatives decides the diameter.
#
# Search arms, chosen at random for each sampled group:
#   * tabu search over best-of-neighbourhood moves (new),
#   * simulated annealing (fallback arm, keeps the older behaviour).
# Cost = unreached (rep, vertex) pairs within DD steps + PEN * duplicate darts.
# Cost 0 is a valid lift. The C side only prints lifts that beat min_n.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXD 64
#define MAXK 6
#define PEN 1000
#define NBR 14
#define TABU_IT 1500
#define TABU_LEN 6
#define SA_IT 4000

typedef struct {
    int K;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

typedef struct {
    int kind;      /* 0: set S[l][i] to val (val then holds old value); 1: swap P[l][i], P[l][i2] */
    int l, i, i2;
    int val;
} Move;

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
static double deadline = 0.0;
static int timed_out = 0;

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
}

static int cost_of(const Cfg *c) {
    int K = c->K, G = GG, N = 2 * K * G;
    for (int v = 0; v < N; v++) g_cnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                if (g_cnt[a] >= Dd || g_cnt[b] >= Dd) return PEN * 1000000;
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
        int head = 0, tail = 0;
        g_vis[src] = g_stamp;
        g_q[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
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

/* Each move is an involution: applying it twice restores the configuration. */
static void apply_move(Cfg *c, Move *m) {
    if (m->kind == 0) {
        int t = c->S[m->l][m->i];
        c->S[m->l][m->i] = m->val;
        m->val = t;
    } else {
        int t = c->P[m->l][m->i];
        c->P[m->l][m->i] = c->P[m->l][m->i2];
        c->P[m->l][m->i2] = t;
    }
}

static void random_move(const Cfg *c, Move *m, int allow_swap_prob4) {
    memset(m, 0, sizeof(*m));
    m->l = rint_(Dd);
    m->i = rint_(c->K);
    if (c->K >= 2 && rint_(allow_swap_prob4) == 0) {
        m->kind = 1;
        m->i2 = rint_(c->K - 1);
        if (m->i2 >= m->i) m->i2++;
    } else {
        m->kind = 0;
        m->val = rint_(GG);
    }
}

/* Tabu search: at each step evaluate NBR random moves and take the best non-tabu one. */
static int tabu_search(Cfg *cur, long iters) {
    static long tabu_until[MAXD][MAXK];
    memset(tabu_until, 0, sizeof(tabu_until));
    int c = cost_of(cur);
    int bestc = c;
    Cfg bestcfg = *cur;
    for (long t = 1; t <= iters && c != 0; t++) {
        if ((t & 31) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        int bc = INT_MAX;
        Move bm;
        memset(&bm, 0, sizeof(bm));
        int have = 0;
        for (int q = 0; q < NBR; q++) {
            Move m;
            random_move(cur, &m, 3);
            if (m.kind == 0 && m.val == cur->S[m.l][m.i]) continue;
            int is_tabu = tabu_until[m.l][m.i] > t;
            apply_move(cur, &m);
            int c2 = cost_of(cur);
            apply_move(cur, &m);
            if (is_tabu && c2 >= bestc) continue;
            if (c2 < bc) {
                bc = c2;
                bm = m;
                have = 1;
            }
        }
        if (!have) continue;
        apply_move(cur, &bm);
        tabu_until[bm.l][bm.i] = t + TABU_LEN;
        c = bc;
        if (c < bestc) {
            bestc = c;
            bestcfg = *cur;
        }
    }
    *cur = bestcfg;
    return bestc;
}

/* Simulated annealing arm. Returns the final cost; cur is left in its final state. */
static int anneal(Cfg *cur, long iters, double T0) {
    int c = cost_of(cur);
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.03;
        Move m;
        random_move(cur, &m, 4);
        apply_move(cur, &m);
        int c2 = cost_of(cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
        } else {
            apply_move(cur, &m);
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

/* Pick k from KF, m = ceil(target / k), and r with r^k = 1 mod m (or r = 1: direct product). */
static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2 && rint_(3) != 0) {
        for (int t = 0; t < 200; t++) {
            long long c = 2 + (long long)rint_((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
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
    for (int w = 0; w < 8; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have_best = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));
    Cfg cur;
    memset(&cur, 0, sizeof(cur));

    while (!timed_out && now_s() < deadline) {
        int rk = rint_(100);
        int Kc = rk < 50 ? 1 : (rk < 78 ? 2 : (rk < 92 ? 3 : (rk < 98 ? 4 : 5)));

        long long gmin = (long long)best_n / (2 * Kc) + 1;
        long long span = gmin / 12 + 2;
        long long target = gmin + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 6000) continue;
        int N = 2 * Kc * GG;
        if (N <= best_n) continue;

        ensure_cap(N);
        cur.K = Kc;
        random_cfg(&cur);

        int c;
        if (rint_(2) == 0) {
            c = tabu_search(&cur, TABU_IT);
        } else {
            c = anneal(&cur, SA_IT, 1.0);
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
# Python glue: exact constructions first, then the C search from the best known order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + max(3.0, min(0.8 * time_limit, time_limit - 8.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        consider(_best_pg(d))
        consider(_araujo(d))
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if D >= 4 and time.monotonic() < budget_end:
        consider(_best_gq(d))
        if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
            return best

    if d >= 3 and D >= 3:
        c_budget = budget_end - time.monotonic() - 2.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
