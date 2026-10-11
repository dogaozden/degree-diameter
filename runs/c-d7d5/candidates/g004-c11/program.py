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


def _cycle(D):
    """Cycle C_{2D}: bipartite, max degree 2, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lifts searched with transitivity-reduced cost.
#
# A lift over G = Z_m x|_r Z_k with K base vertices per side. Left multiplication
# by G is an automorphism, so reachability from the K+K base representatives
# (identity element of each orbit) decides diameter for the whole graph. The
# cost therefore needs only 2K BFS runs instead of 2KG.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Layer l contributes the dart
# (i, P[l][i], S[l][i]) joining A_{i,g} to B_{P[l][i], g*S[l][i]} for all g.
# Each vertex then has degree Dd exactly. Duplicates are penalised.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXN 40000
#define PEN 1000
#define ITERS 6000

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
static int gpow[64];

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k + b, (a,b)(c,d) = (a + r^b c, b + d). */
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

static int capN = 0;
static int *adj = NULL, *cnt = NULL, *vis = NULL, *qu = NULL;
static int vstamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(adj);
    free(cnt);
    free(vis);
    free(qu);
    capN = N;
    adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    cnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N);
    if (!adj || !cnt || !vis || !qu) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

/* Cost = (unreached pairs from base representatives) + PEN * duplicate darts. */
static long cost_of(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
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
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long unreached = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G; /* identity of the orbit representative */
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        qu[tail++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qu[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = adj[u * Dd + t];
                    if (vis[v] != vstamp) {
                        vis[v] = vstamp;
                        qu[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + (long)PEN * dup;
}

static Cfg cur, best_cfg;
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

static long anneal(long iters, double T0) {
    long c = cost_of(&cur);
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        int l = rint_(Dd);
        int i = rint_(cur.K);
        int swap_kind = (cur.K >= 2 && rint_(3) == 0);
        if (swap_kind) {
            int i2 = rint_(cur.K - 1);
            if (i2 >= i) i2++;
            int tmp = cur.P[l][i];
            cur.P[l][i] = cur.P[l][i2];
            cur.P[l][i2] = tmp;
            long c2 = cost_of(&cur);
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                tmp = cur.P[l][i];
                cur.P[l][i] = cur.P[l][i2];
                cur.P[l][i2] = tmp;
            }
        } else {
            int old = cur.S[l][i];
            cur.S[l][i] = rint_(cur.G);
            long c2 = cost_of(&cur);
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
                c = c2;
            } else {
                cur.S[l][i] = old;
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

/* Pick a semidirect factor k, then m with m*k >= target; r = 1 (direct product) half the time. */
static void sample_group(long long target, int *oM, int *oK, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2 && rint_(2) == 0) {
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
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    best_n = min_n;

    while (!timed_out && now_s() < deadline) {
        int rk = rint_(100);
        int Kc = rk < 40 ? 1 : (rk < 70 ? 2 : (rk < 85 ? 3 : (rk < 95 ? 4 : 6)));
        if (Kc > MAXK) Kc = MAXK;

        /* Ratchet: group orders sampled just above what is needed to beat best_n. */
        long long gmin = (long long)best_n / (2LL * Kc) + 1;
        long long span = gmin / 20 + 2;
        long long target = gmin + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        long long N = 2LL * Kc * GG;
        if (N > MAXN || N <= best_n) continue;

        cur.K = Kc;
        cur.G = GG;
        ensure_cap((int)N);
        random_cfg(&cur);
        long c = anneal(ITERS, 1.5);
        /* Cheap second chance: reheat once from the final state. */
        if (c != 0 && !timed_out) c = anneal(ITERS / 2, 0.7);
        if (c == 0 && N > best_n) {
            best_n = (int)N;
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
# Python glue: exact constructions first, then the C search seeded by the best order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Keep a margin for process start-up, compilation check and parsing.
    deadline = start + max(3.0, time_limit - 8.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        consider(*_cycle(D))
        if lib.is_valid(best[0], best[1], d, D):
            return best

    # Exact constructions for calibration-style cases.
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

    # Main search in C, with the best known order as a lower bound.
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
