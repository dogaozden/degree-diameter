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
# New idea: unbalanced bi-Cayley lifts with degree-preserving dart moves.
#
# A base bipartite multigraph has KA "A-side" and KB "B-side" vertices (KA may
# differ from KB) and E darts (ai, bj, s). Dart e joins A_{ai,g} to B_{bj,g*s}
# for every g in G = Z_m x|_r Z_k. Vertices: A-block i is i*G+g, B-block j is
# (KA+j)*G+g, so the order is (KA+KB)*G. Left multiplication by G is an
# automorphism, so BFS from one representative per block decides the diameter.
#
# Degree sequences on each side are fixed at start (each <= Dd). Moves keep them:
# change a voltage, swap the B-endpoints of two darts, or swap the A-endpoints
# of two darts. Cost = unreached (block rep, vertex) pairs within DD steps plus
# PEN * duplicate darts. Balanced K x K shapes are a special case, so the
# search can fall back to the earlier family.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXB 6
#define MAXE 400
#define PEN 1000
#define ITERS 6000

typedef struct {
    int KA, KB, E, G;
    int ai[MAXE], bj[MAXE], s[MAXE];
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

/* Group Z_m x|_r Z_k, element (a,b) coded as a*k + b, product (a,b)(c,d) = (a + r^b c, b + d). */
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
    int KA = c->KA, KB = c->KB, E = c->E, G = c->G;
    int B = KA + KB, N = B * G;
    memset(g_cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int a = c->ai[e], b = KA + c->bj[e], s = c->s[e];
        for (int g = 0; g < G; g++) {
            int x = a * G + g;
            int y = b * G + gmul(g, s);
            g_adj[x * Dd + g_cnt[x]++] = y;
            g_adj[y * Dd + g_cnt[y]++] = x;
        }
    }
    int dup = 0;
    for (int e = 0; e < E; e++)
        for (int f = e + 1; f < E; f++)
            if (c->ai[e] == c->ai[f] && c->bj[e] == c->bj[f] && c->s[e] == c->s[f])
                dup++;

    long unreached = 0;
    for (int r = 0; r < B; r++) {
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
                int dc = g_cnt[u];
                for (int t = 0; t < dc; t++) {
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

static Cfg cur, best_cfg;
static int have_best = 0, best_n = 0;
static int bM = 1, bK = 1, bR = 1;
static double deadline = 0.0;
static int timed_out = 0;

/* Random degree sequence on n vertices: each in [1, Dd], summing to E. */
static void random_degrees(int n, int E, int *deg) {
    for (int i = 0; i < n; i++) deg[i] = 1;
    int rem = E - n;
    while (rem > 0) {
        int i = rint_(n);
        if (deg[i] < Dd) {
            deg[i]++;
            rem--;
        }
    }
}

static void random_cfg(Cfg *c) {
    int dA[MAXB], dB[MAXB];
    int listA[MAXE], listB[MAXE];
    random_degrees(c->KA, c->E, dA);
    random_degrees(c->KB, c->E, dB);
    int p = 0;
    for (int i = 0; i < c->KA; i++)
        for (int k = 0; k < dA[i]; k++) listA[p++] = i;
    p = 0;
    for (int j = 0; j < c->KB; j++)
        for (int k = 0; k < dB[j]; k++) listB[p++] = j;
    for (int i = c->E - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = listB[i];
        listB[i] = listB[j];
        listB[j] = t;
    }
    for (int e = 0; e < c->E; e++) {
        c->ai[e] = listA[e];
        c->bj[e] = listB[e];
        c->s[e] = rint_(c->G);
    }
}

static int anneal(long iters, double T0) {
    int c = cost_of(&cur);
    int E = cur.E;
    for (long t = 0; t < iters && c != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) {
            timed_out = 1;
            break;
        }
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.03;
        int kind = rint_(3);
        int e = rint_(E), f = rint_(E);
        int oe_s = 0, oe_b = 0, of_b = 0, oe_a = 0, of_a = 0;
        if (kind == 0) {
            oe_s = cur.s[e];
            cur.s[e] = rint_(cur.G);
        } else if (kind == 1) {
            if (cur.bj[e] == cur.bj[f]) continue;
            oe_b = cur.bj[e];
            of_b = cur.bj[f];
            cur.bj[e] = of_b;
            cur.bj[f] = oe_b;
        } else {
            if (cur.ai[e] == cur.ai[f]) continue;
            oe_a = cur.ai[e];
            of_a = cur.ai[f];
            cur.ai[e] = of_a;
            cur.ai[f] = oe_a;
        }
        int c2 = cost_of(&cur);
        if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / temp)) {
            c = c2;
        } else {
            if (kind == 0) {
                cur.s[e] = oe_s;
            } else if (kind == 1) {
                cur.bj[e] = oe_b;
                cur.bj[f] = of_b;
            } else {
                cur.ai[e] = oe_a;
                cur.ai[f] = of_a;
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

/* Shape: KA, KB base vertices per side (unbalanced allowed) and E darts. */
static int sample_shape(int *KA, int *KB, int *E) {
    static const int SZ[] = {1, 1, 2, 2, 2, 3, 3, 4};
    int ka = SZ[rint_(8)];
    int kb = SZ[rint_(8)];
    int lo = ka > kb ? ka : kb;
    int mn = ka < kb ? ka : kb;
    int hi = Dd * mn;
    if (hi < lo || hi > MAXE) return 0;
    int lo2 = hi / 2;
    if (lo2 < lo) lo2 = lo;
    int e = (rint_(2) == 0) ? hi : lo2 + rint_(hi - lo2 + 1);
    *KA = ka;
    *KB = kb;
    *E = e;
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
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;
    best_n = min_n;

    while (!timed_out && now_s() < deadline) {
        int KA, KB, E;
        if (!sample_shape(&KA, &KB, &E)) continue;
        int B = KA + KB;

        /* Ratchet: target group orders just above the best total order so far. */
        long long gmin = (long long)best_n / B + 1;
        long long span = gmin / 40 + 2;
        long long target = gmin + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(target, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 6000) continue;
        int N = B * GG;
        if (N <= best_n) continue;

        cur.KA = KA;
        cur.KB = KB;
        cur.E = E;
        cur.G = GG;
        ensure_cap(N);
        random_cfg(&cur);
        int c = anneal(ITERS, 1.2);
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
    int G = best_cfg.G;
    int BB = best_cfg.KA + best_cfg.KB;
    int n = BB * G;
    long m = (long)best_cfg.E * G;
    printf("%d %ld\n", n, m);
    for (int e = 0; e < best_cfg.E; e++) {
        int a = best_cfg.ai[e];
        int b = best_cfg.KA + best_cfg.bj[e];
        int s = best_cfg.s[e];
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", a * G + g, b * G + gmul(g, s));
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
    deadline = start + max(4.0, min(0.85 * time_limit, time_limit - 7.0))

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

    # Main search in C (unbalanced bi-Cayley lifts), seeded with the best known order.
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
