import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines.
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
# C engine: bi-Cayley lifts over Z_m x|_r Z_k with base size K up to 8 per side,
# searched by TABU SEARCH over full move neighbourhoods (sampled), with stall
# perturbation. This replaces the earlier annealing + coordinate polish.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h.
# For each layer l, P[l] is a PERMUTATION of 0..K-1 and dart (l,i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Every vertex then has degree exactly Dd.
# Cost = unreached (representative, vertex) pairs within DD steps + PEN * duplicates.
# Cost 0 means the lift has diameter <= DD. Only the 2K block representatives
# need BFS, because left multiplication by G is an automorphism.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 16
#define MAXK 8
#define MAXN 24000
#define PEN 1000
#define NB 48
#define STALL 150
#define BIG (1L << 60)

typedef struct { int P[MAXD][MAXK]; int S[MAXD][MAXK]; } Cfg;
typedef struct { int type, l, i, i2, old, nw; } Move;

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

static int Dd = 3, DD = 3, K = 1, G = 1, GM = 1, GK = 1, GG = 1;
static int gpow[512];
static int adj[MAXN * MAXD];
static int cnt[MAXN];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;
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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void build_adj(const Cfg *c) {
    int N = 2 * K * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adj[a * Dd + cnt[a]++] = b;
                adj[b * Dd + cnt[b]++] = a;
            }
        }
    }
}

static int dup_count(const Cfg *c) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;
    return dup;
}

static long eval_cost(const Cfg *c) {
    int N = 2 * K * G;
    build_adj(c);
    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        stamp++;
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + (long)PEN * (long)dup_count(c);
}

static void random_cfg(Cfg *c) {
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

static Move rand_move(const Cfg *c) {
    Move mv;
    if (K >= 2 && rint_(3) == 0) {
        mv.type = 0;
        mv.l = rint_(Dd);
        mv.i = rint_(K);
        mv.i2 = rint_(K - 1);
        if (mv.i2 >= mv.i) mv.i2++;
        mv.old = 0;
        mv.nw = 0;
    } else {
        mv.type = 1;
        mv.l = rint_(Dd);
        mv.i = rint_(K);
        mv.i2 = 0;
        mv.old = c->S[mv.l][mv.i];
        mv.nw = rint_(GG);
        if (GG > 1 && mv.nw == mv.old) mv.nw = (mv.nw + 1 + rint_(GG - 1)) % GG;
    }
    return mv;
}

static void apply_mv(Cfg *c, const Move *m) {
    if (m->type == 0) {
        int t = c->P[m->l][m->i];
        c->P[m->l][m->i] = c->P[m->l][m->i2];
        c->P[m->l][m->i2] = t;
    } else {
        c->S[m->l][m->i] = m->nw;
    }
}

static void undo_mv(Cfg *c, const Move *m) {
    if (m->type == 0) {
        int t = c->P[m->l][m->i];
        c->P[m->l][m->i] = c->P[m->l][m->i2];
        c->P[m->l][m->i2] = t;
    } else {
        c->S[m->l][m->i] = m->old;
    }
}

/* Tabu search over sampled neighbourhoods. Returns best cost; *c is set to the best state. */
static long tabu_run(Cfg *c, double t_end, long max_iters) {
    static long tabu_until[MAXD][MAXK];
    memset(tabu_until, 0, sizeof(tabu_until));
    long cur = eval_cost(c);
    long bestc = cur;
    Cfg best = *c;
    long it = 0, stall = 0;
    while (cur != 0 && it < max_iters && now_s() < t_end) {
        it++;
        Move bm;
        long bcost = BIG;
        int have = 0;
        for (int t = 0; t < NB; t++) {
            Move mv = rand_move(c);
            apply_mv(c, &mv);
            long cc = eval_cost(c);
            undo_mv(c, &mv);
            int tb = tabu_until[mv.l][mv.i] > it ||
                     (mv.type == 0 && tabu_until[mv.l][mv.i2] > it);
            if (tb && cc >= bestc) continue;
            if (!have || cc < bcost || (cc == bcost && rint_(2))) {
                bm = mv;
                bcost = cc;
                have = 1;
            }
        }
        if (!have) continue;
        apply_mv(c, &bm);
        cur = bcost;
        long ten = 2 + rint_(6);
        tabu_until[bm.l][bm.i] = it + ten;
        if (bm.type == 0) tabu_until[bm.l][bm.i2] = it + ten;
        if (cur < bestc) {
            bestc = cur;
            best = *c;
            stall = 0;
        } else if (++stall > STALL) {
            for (int t = 0; t < 3; t++) {
                Move mv = rand_move(c);
                apply_mv(c, &mv);
            }
            cur = eval_cost(c);
            stall = 0;
        }
    }
    *c = best;
    return bestc;
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

static void sample_group(long long target, int *oM, int *oK, int *oR) {
    static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                             18, 20, 21, 24, 27, 28, 30, 32, 36, 40};
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
    long min_n = argc > 5 ? atol(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    long best_n = min_n;
    int have = 0;
    int bK = 1, bM = 1, bKk = 1, bR = 1, bG = 1;
    static const int KS[] = {1, 2, 2, 3, 3, 4, 4, 5, 6};
    Cfg best_cfg;
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int k = KS[rint_((int)(sizeof(KS) / sizeof(KS[0])))];
        if (k > MAXK) k = MAXK;
        long g0 = best_n / (2 * k) + 1;
        long span = g0 / 20 + 6;
        long g = g0 + (long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        if ((long)M * Kk > MAXN / (2 * k)) continue;
        set_group(M, Kk, R);
        K = k;
        G = GG;
        long N = 2L * K * G;
        if (N <= best_n || N > MAXN) continue;

        double remain = deadline - now_s();
        if (remain < 0.2) break;
        double budget = remain * 0.2;
        if (budget < 1.0) budget = 1.0;
        if (budget > 6.0) budget = 6.0;
        if (budget > remain) budget = remain;

        Cfg c;
        memset(&c, 0, sizeof(c));
        random_cfg(&c);
        long res = tabu_run(&c, now_s() + budget, 1000000L);
        if (res == 0) {
            best_n = N;
            best_cfg = c;
            bK = K;
            bM = M;
            bKk = Kk;
            bR = R;
            bG = G;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bKk, bR);
    K = bK;
    G = bG;
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
# Python glue: exact constructions first (always valid fallbacks), then tabu search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Tabu search over bi-Cayley lifts, seeded with the best known order as a lower bound.
    # Leave room for the one-off C compile, which happens inside run_c.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 2.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=time_limit - 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
