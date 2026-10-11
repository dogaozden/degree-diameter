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
# C engine.
#   Mode 0 (default): bi-Cayley search with breakout local search (clause
#     weighting), a unit-weight coordinate polish for near-solutions, and
#     iterated local search on the best near-miss.
#   Mode 1 (new): grow-and-anneal on a general valid bipartite graph read from
#     stdin. Each growth step adds one vertex per side, fills the two new
#     vertices to full degree by edge transfers (which leave every old degree
#     unchanged), then runs simulated annealing with degree- and
#     bipartition-preserving 2-switches to remove all pairs farther than D.
#     The grown graph is kept only when it has zero bad pairs.
#
# Mode 0 vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
# A_{i,g} to B_{P[l][i], g*S[l][i]}. Raw cost = unreached rep-vertex pairs
# within DD steps + PEN * duplicate darts. Cost 0 means a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 3
#define PEN 1000
#define POLISH_T 80
#define STUCK 50
#define BREAK_ITERS 25000
#define NEAR_PCT 50
#define PERTURB 3

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

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static int cap = 0;
static int *g_adj = NULL, *g_cnt = NULL, *g_vis = NULL, *g_q = NULL;
static long long *g_w = NULL;
static int g_stamp = 0;
static long long g_rawcost = 0;
static int g_dup = 0;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(g_adj);
    free(g_cnt);
    free(g_vis);
    free(g_q);
    free(g_w);
    cap = N;
    g_adj = malloc(sizeof(int) * (size_t)N * (size_t)Dd);
    g_cnt = malloc(sizeof(int) * (size_t)N);
    g_vis = calloc((size_t)N, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)N);
    g_w = malloc(sizeof(long long) * (size_t)4 * (size_t)N);
    if (!g_adj || !g_cnt || !g_vis || !g_q || !g_w) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    g_stamp = 0;
}

static void reset_weights(int K, int N) {
    long long total = (long long)2 * K * N;
    for (long long j = 0; j < total; j++) g_w[j] = 1;
}

/* Returns weighted cost (sum of weights of unreached pairs + PEN * dups).
   Sets g_rawcost to the unweighted cost. If bump != 0, the weight of every
   currently unreached pair is increased by one. */
static long long cost_of(const Cfg *c, int bump) {
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

    long long wsum = 0, raw = 0;
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
        long long *w = g_w + (size_t)r * (size_t)N;
        for (int v = 0; v < N; v++) {
            if (g_vis[v] != g_stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_dup = dup;
    g_rawcost = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
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

/* Breakout local search on weighted cost. Returns the best raw cost seen;
   leaves *c at that best state. */
static long long breakout(Cfg *c, long iters) {
    long long wc = cost_of(c, 0);
    long long rc = g_rawcost;
    long long bestraw = rc;
    Cfg bc = *c;
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
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
        long long wc2 = cost_of(c, 0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            rc = g_rawcost;
            if (rc < bestraw) {
                bestraw = rc;
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
            stuck++;
        }
        if (stuck >= STUCK) {
            cost_of(c, 1);              /* raise weights of unreached pairs */
            wc = cost_of(c, 0);
            rc = g_rawcost;
            stuck = 0;
        }
    }
    *c = bc;
    return bestraw;
}

/* Best-improvement coordinate sweeps over every single dart value, with
   unit weights (weights must be reset before calling). */
static long long polish(Cfg *c) {
    long long cost = cost_of(c, 0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < Dd && cost != 0; l++) {
            for (int i = 0; i < c->K; i++) {
                if (now_s() > deadline) return cost;
                int old = c->S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < GG; s++) {
                    if (s == old) continue;
                    c->S[l][i] = s;
                    long long c2 = cost_of(c, 0);
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
                         18, 20, 21, 24, 27, 28, 30, 32, 36, 40};

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

/* ============================ Mode 1: grow and anneal ============================ */

#define AN_CAPN 6000
#define AN_ITERS 4000
#define AN_T0 1.2

static int an_cap = 0, an_W = 0, an_n = 0;
static int *an_adj = NULL, *an_deg = NULL, *an_side = NULL;
static int *bs_adj = NULL, *bs_deg = NULL, bs_n = 0;
static int *ta_adj = NULL, *ta_deg = NULL;
static uint64_t *an_R0 = NULL, *an_R1 = NULL;

static void an_alloc(int cap) {
    an_cap = cap;
    an_W = (cap + 63) / 64;
    an_adj = calloc((size_t)cap * (size_t)Dd, sizeof(int));
    an_deg = calloc((size_t)cap, sizeof(int));
    an_side = calloc((size_t)cap, sizeof(int));
    bs_adj = calloc((size_t)cap * (size_t)Dd, sizeof(int));
    bs_deg = calloc((size_t)cap, sizeof(int));
    ta_adj = calloc((size_t)cap * (size_t)Dd, sizeof(int));
    ta_deg = calloc((size_t)cap, sizeof(int));
    an_R0 = calloc((size_t)cap * (size_t)an_W, sizeof(uint64_t));
    an_R1 = calloc((size_t)cap * (size_t)an_W, sizeof(uint64_t));
    if (!an_adj || !an_deg || !an_side || !bs_adj || !bs_deg || !ta_adj || !ta_deg ||
        !an_R0 || !an_R1) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int an_has(int u, int v) {
    for (int k = 0; k < an_deg[u]; k++)
        if (an_adj[u * Dd + k] == v) return 1;
    return 0;
}

static void an_add(int u, int v) {
    an_adj[u * Dd + an_deg[u]++] = v;
    an_adj[v * Dd + an_deg[v]++] = u;
}

static void an_rem1(int u, int v) {
    int dg = an_deg[u];
    for (int k = 0; k < dg; k++) {
        if (an_adj[u * Dd + k] == v) {
            an_adj[u * Dd + k] = an_adj[u * Dd + dg - 1];
            an_deg[u]--;
            return;
        }
    }
}

static void an_del(int u, int v) {
    an_rem1(u, v);
    an_rem1(v, u);
}

static int an_pick_side(int s) {
    int v;
    do {
        v = rint_(an_n);
    } while (an_side[v] != s);
    return v;
}

/* Number of unordered pairs at distance > DD (bitset BFS on the first an_n vertices). */
static long long an_cost(void) {
    int n = an_n;
    int W = (n + 63) >> 6;
    uint64_t *A = an_R0, *B = an_R1;
    memset(A, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) A[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = B + (size_t)v * W;
            uint64_t *src = A + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            int dg = an_deg[v];
            for (int k = 0; k < dg; k++) {
                const uint64_t *su = A + (size_t)an_adj[v * Dd + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
            for (int w = 0; w < W; w++)
                if (dst[w] != src[w]) changed = 1;
        }
        uint64_t *tmp = A;
        A = B;
        B = tmp;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = A + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc64(row[w]);
        bad += n - c;
    }
    return bad / 2;
}

static void an_save(int *dadj, int *ddeg) {
    memcpy(dadj, an_adj, sizeof(int) * (size_t)an_n * (size_t)Dd);
    memcpy(ddeg, an_deg, sizeof(int) * (size_t)an_n);
}

static void an_load(const int *sadj, const int *sdeg, int n) {
    an_n = n;
    memcpy(an_adj, sadj, sizeof(int) * (size_t)n * (size_t)Dd);
    memcpy(an_deg, sdeg, sizeof(int) * (size_t)n);
}

/* Simulated annealing with degree- and bipartition-preserving 2-switches.
   Returns the best cost reached; the working state is left at the best state. */
static long long an_anneal(long iters, double T0) {
    int bn = an_n;
    long long cur = an_cost();
    long long best = cur;
    an_save(ta_adj, ta_deg);
    for (long t = 0; t < iters && best > 0; t++) {
        if ((t & 31) == 0 && now_s() > deadline) break;
        double T = T0 * (1.0 - (double)t / (double)iters) + 0.02;
        int u1 = an_pick_side(0), u2 = an_pick_side(0);
        if (an_deg[u1] == 0 || an_deg[u2] == 0) continue;
        int v1 = an_adj[u1 * Dd + rint_(an_deg[u1])];
        int v2 = an_adj[u2 * Dd + rint_(an_deg[u2])];
        if (u1 == u2 || v1 == v2) continue;
        if (an_has(u1, v2) || an_has(u2, v1)) continue;
        an_del(u1, v1);
        an_del(u2, v2);
        an_add(u1, v2);
        an_add(u2, v1);
        long long c2 = an_cost();
        int acc = (c2 <= cur);
        if (!acc) {
            double r = (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
            acc = r < exp((double)(cur - c2) / T);
        }
        if (acc) {
            cur = c2;
            if (cur < best) {
                best = cur;
                an_save(ta_adj, ta_deg);
            }
        } else {
            an_del(u1, v2);
            an_del(u2, v1);
            an_add(u1, v1);
            an_add(u2, v2);
        }
    }
    an_load(ta_adj, ta_deg, bn);
    return best;
}

static void an_print(void) {
    int n = bs_n;
    long cnt = 0;
    for (int u = 0; u < n; u++)
        if (an_side[u] == 0) cnt += bs_deg[u];
    printf("%d %ld\n", n, cnt);
    for (int u = 0; u < n; u++) {
        if (an_side[u] != 0) continue;
        for (int k = 0; k < bs_deg[u]; k++)
            printf("%d %d\n", u, bs_adj[u * Dd + k]);
    }
}

static int anneal_main(double tl) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > AN_CAPN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    an_alloc(AN_CAPN);
    an_n = n;
    for (int v = 0; v < n; v++) an_deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            an_deg[u] >= Dd || an_deg[v] >= Dd) {
            printf("0 0\n");
            return 0;
        }
        if (an_has(u, v)) continue;
        an_add(u, v);
    }

    /* Bipartition by BFS; an odd cycle means the input is not usable. */
    int *q = malloc(sizeof(int) * (size_t)n);
    if (!q) return 1;
    for (int v = 0; v < n; v++) an_side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (an_side[s] != -1) continue;
        an_side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < an_deg[u]; k++) {
                int w = an_adj[u * Dd + k];
                if (an_side[w] == -1) {
                    an_side[w] = 1 - an_side[u];
                    q[qt++] = w;
                } else if (an_side[w] == an_side[u]) {
                    printf("0 0\n");
                    free(q);
                    return 0;
                }
            }
        }
    }
    free(q);

    deadline = now_s() + tl;
    long long c = an_cost();
    if (c != 0) c = an_anneal(AN_ITERS * 4, AN_T0);
    if (c != 0) {
        printf("0 0\n");
        return 0;
    }
    an_save(bs_adj, bs_deg);
    bs_n = n;

    while (now_s() < deadline) {
        if (bs_n + 2 > an_cap) break;
        an_load(bs_adj, bs_deg, bs_n);
        int a = bs_n, b = bs_n + 1;
        an_n = bs_n + 2;
        an_side[a] = 0;
        an_side[b] = 1;
        an_deg[a] = 0;
        an_deg[b] = 0;
        an_add(a, b);
        /* Fill a and b to degree Dd: remove (u,v), add (a,v) and (u,b). */
        int ok = 1;
        for (int s = 0; s < Dd - 1 && ok; s++) {
            int done = 0;
            for (int tries = 0; tries < 4000 && !done; tries++) {
                int u = an_pick_side(0);
                if (u == a || an_deg[u] == 0 || an_has(u, b)) continue;
                int v = an_adj[u * Dd + rint_(an_deg[u])];
                if (v == b || an_has(a, v)) continue;
                an_del(u, v);
                an_add(a, v);
                an_add(u, b);
                done = 1;
            }
            if (!done) ok = 0;
        }
        if (!ok) continue;
        long long cc = an_cost();
        if (cc != 0) cc = an_anneal(AN_ITERS, AN_T0);
        if (cc == 0) {
            an_save(bs_adj, bs_deg);
            bs_n = an_n;
        }
    }
    an_print();
    return 0;
}

/* ================================== main ================================== */

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;
    int mode = argc > 6 ? atoi(argv[6]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    if (mode == 1) return anneal_main(tl);

    double t0 = now_s();
    deadline = t0 + tl;
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    /* Best near-miss (smallest raw cost, still above best_n) kept for ILS. */
    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;

    while (now_s() < deadline) {
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
            /* Perturb the stored near-miss in its own group. */
            K = near.K;
            M = nM;
            Kk = nK;
            R = nR;
            set_group(M, Kk, R);
            cur = near;
            for (int t = 0; t < PERTURB; t++) {
                int l = rint_(Dd);
                int i = rint_(K);
                cur.S[l][i] = rint_(GG);
            }
        } else {
            /* Mostly K = 1 (bi-Cayley), sometimes K = 2. The share of K = 2
               grows from 25% to 50% with consecutive failures. The window
               above best_n widens with failures, capped at g0/3. */
            int k2_pct = 25 + (fails / 20) * 5;
            if (k2_pct > 50) k2_pct = 50;
            K = (rint_(100) < 100 - k2_pct) ? 1 : 2;
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 25 + 6 + (long long)(fails / 40) * (g0 / 50 + 1);
            if (span > g0 / 3 + 6) span = g0 / 3 + 6;
            long long g = g0 + (long long)rint_((int)span);
            sample_group(g, &M, &Kk, &R);
            set_group(M, Kk, R);
            if (GG > 6000) continue;
            cur.K = K;
            cur.G = GG;
            random_cfg(&cur);
        }

        int N = 2 * K * GG;
        if (N <= best_n) {
            have_near = 0;
            continue;
        }
        ensure_cap(N);
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        long long thr = (long long)POLISH_T;
        if ((long long)N / 4 > thr) thr = (long long)N / 4;
        if (g_rawcost > 0 && g_rawcost <= thr) {
            reset_weights(K, N);
            polish(&cur);
        }
        cost_of(&cur, 0);
        if (g_rawcost == 0) {
            best_n = N;
            best_cfg = cur;
            bM = M;
            bK = Kk;
            bR = R;
            have = 1;
            have_near = 0;
            fails = 0;
        } else {
            fails++;
            if (!have_near || g_rawcost <= nraw) {
                near = cur;
                nM = M;
                nK = Kk;
                nR = R;
                nraw = g_rawcost;
                have_near = 1;
            }
        }
    }

    if (!have) {
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
# Python glue: exact constructions, then bi-Cayley search, then grow-and-anneal.
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

    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 1.5

        # Phase 1: bi-Cayley search seeded with the best known order.
        if remaining >= 2.0:
            c1 = 0.45 * remaining if remaining >= 6.0 else remaining
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c1:.2f}", best_n, 0],
                                timeout=c1 + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Phase 2: grow the best valid graph by vertex pairs and anneal.
        remaining = deadline - time.monotonic() - 1.5
        if remaining >= 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed + 1, f"{remaining:.2f}", 0, 1],
                                stdin_graph=best, timeout=remaining + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
