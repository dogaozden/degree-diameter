import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (safe fallbacks).
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
# C engine: multi-base-vertex group lifts searched by TABU search.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, for base indices i,j < K.
# Layer l (0..Dd-1) joins A_{i,g} to B_{P[l][i], g*S[l][i]} for all g.
# Each P[l] is a permutation, so the lift is Dd-regular and bipartite.
# Left multiplication by the group is an automorphism, so one representative
# per block suffices for the distance check. Cost = unreached rep-pairs within
# DD steps + PEN * duplicate darts. Cost 0 means a valid graph.
#
# Differences from the previous engine:
#  * tabu search over sampled moves (best admissible move each step) instead of
#    simulated annealing;
#  * base graphs with up to 6 vertices per side;
#  * restarts from fresh random configurations, with the target group order
#    raised past the best order found so far.
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
#define TABU_LEN 9
#define NB_SAMPLE 40
#define TABU_ITERS 2500
#define MAXN_LIMIT 9000

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

typedef struct {
    int type, l, i, i2, val, old;
} Move;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

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

/* Semidirect product Z_m x|_r Z_k, element a*k+b, (a,b)(c,d) = (a + r^b c, b+d). */
static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
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

static Move rand_move(const Cfg *c) {
    Move m;
    m.type = 0;
    m.l = rint_(Dd);
    m.i = rint_(c->K);
    m.i2 = m.i;
    m.val = 0;
    m.old = 0;
    if (c->K >= 2 && rint_(3) == 0) {
        m.type = 1;
        m.i2 = rint_(c->K - 1);
        if (m.i2 >= m.i) m.i2++;
    } else {
        m.val = rint_(c->G);
    }
    return m;
}

static void apply_move(Cfg *c, Move *m) {
    if (m->type == 0) {
        m->old = c->S[m->l][m->i];
        c->S[m->l][m->i] = m->val;
    } else {
        int t = c->P[m->l][m->i];
        c->P[m->l][m->i] = c->P[m->l][m->i2];
        c->P[m->l][m->i2] = t;
    }
}

static void undo_move(Cfg *c, const Move *m) {
    if (m->type == 0) {
        c->S[m->l][m->i] = m->old;
    } else {
        int t = c->P[m->l][m->i];
        c->P[m->l][m->i] = c->P[m->l][m->i2];
        c->P[m->l][m->i2] = t;
    }
}

/* Tabu search: each step evaluates NB_SAMPLE random moves and applies the best
   admissible one (aspiration allows tabu moves that beat the best cost). */
static int tabu_run(Cfg *c, long iters) {
    static long tb[MAXD][MAXK];
    memset(tb, 0, sizeof tb);
    int cur = cost_of(c);
    int best = cur;
    Cfg bc = *c;
    for (long it = 1; it <= iters && cur != 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        int bestc = 1 << 30;
        Move bm;
        int have = 0;
        for (int s = 0; s < NB_SAMPLE; s++) {
            Move m = rand_move(c);
            int is_tabu = tb[m.l][m.i] > it || (m.type == 1 && tb[m.l][m.i2] > it);
            apply_move(c, &m);
            int c2 = cost_of(c);
            undo_move(c, &m);
            if (is_tabu && c2 >= best) continue;
            if (c2 < bestc || (c2 == bestc && rint_(2) == 0)) {
                bestc = c2;
                bm = m;
                have = 1;
            }
        }
        if (!have) continue;
        apply_move(c, &bm);
        cur = bestc;
        long ten = it + TABU_LEN + rint_(TABU_LEN);
        tb[bm.l][bm.i] = ten;
        if (bm.type == 1) tb[bm.l][bm.i2] = ten;
        if (cur < best) {
            best = cur;
            bc = *c;
        }
    }
    *c = bc;
    return best;
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

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16, 18, 20,
                         21, 24, 28, 30, 32, 36, 40, 42, 48};

/* Pick k from KF, m = ceil(target/k), and r with gcd(r,m)=1 and r^k = 1 mod m
   (falls back to r = 1, the direct product, if none is found). */
static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
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
    int have = 0;
    int bM = 1, bKk = 1, bR = 1;
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    static const int KB[] = {1, 1, 1, 1, 2, 2, 2, 3, 4, 5, 6};
    int nkb = (int)(sizeof(KB) / sizeof(KB[0]));

    while (now_s() < deadline) {
        int K = KB[rint_(nkb)];
        if (K > MAXK) K = MAXK;
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 30 + 4;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        long long Nll = 2LL * K * GG;
        if (Nll > MAXN_LIMIT) continue;
        int N = (int)Nll;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = GG;
        ensure_cap(N);
        random_cfg(&cur);
        int c = tabu_run(&cur, TABU_ITERS);
        if (c == 0) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bKk = Kk;
            bR = R;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bKk, bR);
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
# Python glue: exact constructions first, then the C search.
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

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass
        if best_n > 0 and lib.is_valid(best[0], best[1], d, D) and D == 3:
            pass

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Randomized tabu search in C, seeded with the best known order as a lower bound.
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
