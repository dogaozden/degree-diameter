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
# C engine: bi-Cayley annealing over a wider family of groups.
#
# Groups now come from two families, both built as multiplication tables:
#  * type 0: Z_m x| Z_k with action r (cyclic when k = 1, direct when r = 1),
#  * type 1: Heisenberg group of order n^3 (nilpotent, non-abelian).
# Base graph uses K = 1..4 vertices per side.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Cost = unreached rep-vertex pairs within
# DD steps + PEN * duplicate darts. Cost 0 means a valid graph.
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
#define PEN 1000
#define POLISH_T 80
#define GMAX 1600

typedef struct {
    int K, G;
    int P[MAXD][MAXK];
    int S[MAXD][MAXK];
} Cfg;

typedef struct {
    int type;   /* 0: Z_m x| Z_k with action r ; 1: Heisenberg mod n */
    int m, k, r, n;
    int G;
} Spec;

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
static int GG = 1;
static int *MT = NULL;
static double deadline = 0.0;
static int ITERS = 40000;

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static int g_stamp = 0;

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

static void build_group(const Spec *sp) {
    int G;
    if (sp->type == 0) {
        int m = sp->m, k = sp->k;
        G = m * k;
        long long pw[64];
        long long p = 1 % m;
        for (int b = 0; b < k; b++) {
            pw[b] = p;
            p = (p * (long long)sp->r) % m;
        }
        GG = G;
        for (int x = 0; x < G; x++) {
            int a1 = x / k, b1 = x % k;
            for (int y = 0; y < G; y++) {
                int a2 = y / k, b2 = y % k;
                long long t = ((long long)a1 + pw[b1] * (long long)a2) % m;
                MT[(size_t)x * G + y] = (int)t * k + (b1 + b2) % k;
            }
        }
    } else {
        int n = sp->n;
        G = n * n * n;
        GG = G;
        for (int x = 0; x < G; x++) {
            int a1 = x / (n * n), b1 = (x / n) % n, c1 = x % n;
            for (int y = 0; y < G; y++) {
                int a2 = y / (n * n), b2 = (y / n) % n, c2 = y % n;
                int a = (a1 + a2) % n;
                int b = (b1 + b2) % n;
                int c = (c1 + c2 + a1 * b2) % n;
                MT[(size_t)x * G + y] = (a * n + b) * n + c;
            }
        }
    }
}

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
                int b = (K + j) * G + MT[(size_t)g * G + s];
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

/* Annealing that returns the best state seen (lowest cost). */
static int anneal(Cfg *c, long iters, double T0) {
    int cost = cost_of(c);
    int bestc = cost;
    Cfg bc = *c;
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 255) == 0 && now_s() > deadline) break;
        double temp = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        int l = rint_(Dd);
        int i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(4) == 0);
        int old_s = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int tmp = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = tmp;
        } else {
            old_s = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        int c2 = cost_of(c);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) {
                bestc = cost;
                bc = *c;
            }
        } else {
            if (kind) {
                int tmp = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = tmp;
            } else {
                c->S[l][i] = old_s;
            }
        }
    }
    *c = bc;
    return bestc;
}

/* Best-improvement coordinate sweeps over every single dart value. */
static int polish(Cfg *c) {
    int cost = cost_of(c);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old, bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    int c2 = cost_of(c);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                c->S[l][i] = bestv;
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                    if (cost == 0) break;
                }
            }
        }
    }
    return cost;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16,
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

/* Sample a group of order in roughly [g0, g0 + span]. Returns 0 on failure. */
static int sample_spec(long long g0, long long span, Spec *sp) {
    if (rint_(100) < 35) {
        long long n = 2;
        while (n * n * n < g0) n++;
        if (rint_(2)) n++;
        if (n * n * n <= GMAX && n * n * n <= g0 * 3 / 2 + 100) {
            sp->type = 1;
            sp->n = (int)n;
            sp->m = 0;
            sp->k = 0;
            sp->r = 0;
            sp->G = (int)(n * n * n);
            return 1;
        }
    }
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rint_(nk)];
    long long target = g0 + (long long)rint_((int)span);
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    if (m * k > GMAX) return 0;
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
    sp->type = 0;
    sp->m = (int)m;
    sp->k = k;
    sp->r = r;
    sp->n = 0;
    sp->G = (int)(m * k);
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

    MT = malloc(sizeof(int) * (size_t)GMAX * (size_t)GMAX);
    if (!MT) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    Spec bsp;
    memset(&bsp, 0, sizeof(bsp));
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int roll = rint_(100);
        int K = roll < 45 ? 1 : (roll < 75 ? 2 : (roll < 90 ? 3 : 4));
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 25 + 6;
        Spec sp;
        if (!sample_spec(g0, span, &sp)) continue;
        build_group(&sp);
        int G = GG;
        int N = 2 * K * G;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = G;
        ensure_cap(N);
        random_cfg(&cur);
        int c = anneal(&cur, ITERS, 1.5);
        if (c > 0 && c <= POLISH_T && K <= 2) c = polish(&cur);
        if (c == 0) {
            best_n = N;
            best_cfg = cur;
            bsp = sp;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    build_group(&bsp);
    int K = best_cfg.K, G = best_cfg.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best_cfg.P[l][i], s = best_cfg.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + MT[(size_t)g * G + s]);
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Randomized group-lift search in C, seeded with the best known order.
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
