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
#  Mode 0 (argv[6] absent or 0): bi-Cayley breakout local search with polish
#    and iterated local search, as before.
#  Mode 1 (argv[6] = 1): NEW growth engine. Reads a valid graph from stdin and
#    repeatedly subdivides a random edge (a-b becomes a-y-x-b with x on a's side,
#    y on b's side). This adds two vertices of degree 2 and leaves deficiency.
#    Simulated annealing then repairs the graph using two degree-preserving
#    moves: an edge switch (v-w, v2-w2 -> v-w2, v2-w) and a deficiency fill
#    (a deficient vertex takes an edge from a full vertex, pushing the deficiency
#    to the other end). The cost is the number of vertex pairs at distance > D,
#    computed with bitset BFS. On failure, the search restores the last valid graph
#    and grows again.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

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

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* ============================================================================
   Growth engine (mode 1): subdivide-and-repair from a valid input graph.
   ============================================================================ */
#define GR_MAXN 4000
#define GR_W ((GR_MAXN + 63) / 64)
#define GR_MAXDEG 16
#define GR_STALL 5000
#define GR_T 0.5
#define GA(v, k) gr_adj[(size_t)(v) * (size_t)gr_d + (size_t)(k)]

static int gr_d = 3, gr_D = 3, gr_n = 0;
static int *gr_adj = NULL, *gr_deg = NULL, *gr_side = NULL;
static int *bk_adj = NULL, *bk_deg = NULL, bk_n = 0;
static int *bs_adj = NULL, *bs_deg = NULL, *bs_side = NULL, bs_n = 0;
static uint64_t *gr_R0 = NULL, *gr_R1 = NULL;
static int gr_defi[GR_MAXN];

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gr_has(int a, int b) {
    for (int k = 0; k < gr_deg[a]; k++)
        if (GA(a, k) == b) return 1;
    return 0;
}

static void gr_drop(int a, int b) {
    for (int k = 0; k < gr_deg[a]; k++) {
        if (GA(a, k) == b) {
            GA(a, k) = GA(a, gr_deg[a] - 1);
            gr_deg[a]--;
            return;
        }
    }
}

static void gr_push(int a, int b) { GA(a, gr_deg[a]++) = b; }

static void gr_del(int a, int b) {
    gr_drop(a, b);
    gr_drop(b, a);
}

static void gr_add(int a, int b) {
    gr_push(a, b);
    gr_push(b, a);
}

static void gr_repl(int a, int old, int nw) {
    for (int k = 0; k < gr_deg[a]; k++) {
        if (GA(a, k) == old) {
            GA(a, k) = nw;
            return;
        }
    }
}

/* Bad pairs (distance > gr_D, unreachable counted) via bitset BFS. */
static long long gr_eval(void) {
    int n = gr_n, nw = (n + 63) >> 6;
    uint64_t *cur = gr_R0, *nxt = gr_R1;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + (size_t)v * GR_W;
        for (int w = 0; w < nw; w++) row[w] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < gr_D; r++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * GR_W;
            const uint64_t *src = cur + (size_t)v * GR_W;
            for (int w = 0; w < nw; w++) dst[w] = src[w];
            for (int k = 0; k < gr_deg[v]; k++) {
                const uint64_t *su = cur + (size_t)GA(v, k) * GR_W;
                for (int w = 0; w < nw; w++) dst[w] |= su[w];
            }
            for (int w = 0; w < nw; w++)
                if (dst[w] != src[w]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = cur + (size_t)v * GR_W;
        int cnt = 0;
        for (int w = 0; w < nw; w++) cnt += popc64(row[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static void gr_save_best(void) {
    memcpy(bs_adj, gr_adj, sizeof(int) * (size_t)gr_n * (size_t)gr_d);
    memcpy(bs_deg, gr_deg, sizeof(int) * (size_t)gr_n);
    memcpy(bs_side, gr_side, sizeof(int) * (size_t)gr_n);
    bs_n = gr_n;
}

static void gr_restore_best(void) {
    memcpy(gr_adj, bs_adj, sizeof(int) * (size_t)bs_n * (size_t)gr_d);
    memcpy(gr_deg, bs_deg, sizeof(int) * (size_t)bs_n);
    memcpy(gr_side, bs_side, sizeof(int) * (size_t)bs_n);
    gr_n = bs_n;
}

static void gr_backup(void) {
    memcpy(bk_adj, gr_adj, sizeof(int) * (size_t)gr_n * (size_t)gr_d);
    memcpy(bk_deg, gr_deg, sizeof(int) * (size_t)gr_n);
    bk_n = gr_n;
}

static void gr_restore(void) {
    memcpy(gr_adj, bk_adj, sizeof(int) * (size_t)bk_n * (size_t)gr_d);
    memcpy(gr_deg, bk_deg, sizeof(int) * (size_t)bk_n);
    gr_n = bk_n;
}

/* Degree-preserving edge switch between opposite-side pairs. */
static int gr_move_switch(void) {
    int n = gr_n;
    int v = rint_(n);
    if (gr_deg[v] == 0) return 0;
    int v2 = -1;
    for (int t = 0; t < 8; t++) {
        int c = rint_(n);
        if (c != v && gr_side[c] == gr_side[v] && gr_deg[c] > 0) {
            v2 = c;
            break;
        }
    }
    if (v2 < 0) return 0;
    int w = GA(v, rint_(gr_deg[v]));
    int w2 = GA(v2, rint_(gr_deg[v2]));
    if (w == w2 || gr_has(v, w2) || gr_has(v2, w)) return 0;
    gr_del(v, w);
    gr_del(v2, w2);
    gr_add(v, w2);
    gr_add(v2, w);
    return 1;
}

/* Deficiency fill: a deficient vertex x gains an edge to w. If w is full,
   w drops one neighbour z, which becomes deficient. */
static int gr_move_fill(void) {
    int n = gr_n, nd = 0;
    for (int v = 0; v < n; v++)
        if (gr_deg[v] < gr_d) gr_defi[nd++] = v;
    if (nd == 0) return 0;
    int x = gr_defi[rint_(nd)];
    int w = -1;
    for (int t = 0; t < 60; t++) {
        int c = rint_(n);
        if (gr_side[c] != gr_side[x] && !gr_has(x, c)) {
            w = c;
            break;
        }
    }
    if (w < 0) return 0;
    if (gr_deg[w] < gr_d) {
        gr_add(x, w);
        return 1;
    }
    int z = GA(w, rint_(gr_deg[w]));
    gr_del(z, w);
    gr_add(x, w);
    return 1;
}

/* Subdivide a random edge a-b into a-y-x-b (x on a's side, y on b's side). */
static int gr_grow(void) {
    if (gr_d < 2 || gr_n + 2 > GR_MAXN) return 0;
    int a = -1;
    for (int t = 0; t < 200; t++) {
        int c = rint_(gr_n);
        if (gr_deg[c] > 0) {
            a = c;
            break;
        }
    }
    if (a < 0) return 0;
    int b = GA(a, rint_(gr_deg[a]));
    int x = gr_n, y = gr_n + 1, sa = gr_side[a];
    gr_side[x] = sa;
    gr_side[y] = 1 - sa;
    gr_repl(a, b, y);
    gr_repl(b, a, x);
    gr_deg[x] = 0;
    gr_deg[y] = 0;
    gr_push(y, a);
    gr_push(y, x);
    gr_push(x, y);
    gr_push(x, b);
    gr_n += 2;
    return 1;
}

static int grow_main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    if (d < 2 || d > GR_MAXDEG || D < 1) {
        printf("0 0\n");
        return 0;
    }
    gr_d = d;
    gr_D = D;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    deadline = now_s() + tl;

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2 || n_in < 1 || n_in > GR_MAXN - 2 || m_in < 0) {
        printf("0 0\n");
        return 0;
    }
    size_t sz = (size_t)GR_MAXN * (size_t)d;
    gr_adj = malloc(sizeof(int) * sz);
    bk_adj = malloc(sizeof(int) * sz);
    bs_adj = malloc(sizeof(int) * sz);
    gr_deg = calloc(GR_MAXN, sizeof(int));
    bk_deg = calloc(GR_MAXN, sizeof(int));
    bs_deg = calloc(GR_MAXN, sizeof(int));
    gr_side = calloc(GR_MAXN, sizeof(int));
    bs_side = calloc(GR_MAXN, sizeof(int));
    gr_R0 = malloc(sizeof(uint64_t) * (size_t)GR_MAXN * GR_W);
    gr_R1 = malloc(sizeof(uint64_t) * (size_t)GR_MAXN * GR_W);
    if (!gr_adj || !bk_adj || !bs_adj || !gr_deg || !bk_deg || !bs_deg ||
        !gr_side || !bs_side || !gr_R0 || !gr_R1) {
        printf("0 0\n");
        return 0;
    }

    gr_n = n_in;
    int bad = 0;
    for (int i = 0; i < m_in; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            bad = 1;
            break;
        }
        if (u < 0 || v < 0 || u >= n_in || v >= n_in || u == v ||
            gr_deg[u] >= d || gr_deg[v] >= d || gr_has(u, v)) {
            bad = 1;
            break;
        }
        gr_add(u, v);
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the input; a conflict means it is not bipartite. */
    for (int v = 0; v < gr_n; v++) gr_side[v] = -1;
    int *stack = malloc(sizeof(int) * (size_t)gr_n);
    if (!stack) {
        printf("0 0\n");
        return 0;
    }
    for (int s = 0; s < gr_n && !bad; s++) {
        if (gr_side[s] != -1) continue;
        gr_side[s] = 0;
        int top = 0;
        stack[top++] = s;
        while (top > 0) {
            int u = stack[--top];
            for (int k = 0; k < gr_deg[u]; k++) {
                int v = GA(u, k);
                if (gr_side[v] == -1) {
                    gr_side[v] = 1 - gr_side[u];
                    stack[top++] = v;
                } else if (gr_side[v] == gr_side[u]) {
                    bad = 1;
                }
            }
        }
    }
    free(stack);
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    long long cost = gr_eval();
    int have = 0;
    if (cost == 0) {
        gr_save_best();
        have = 1;
    }
    long long lvl = cost;
    long long stall = 0;

    while (now_s() < deadline) {
        if (cost == 0) {
            gr_save_best();
            have = 1;
            if (!gr_grow()) break;
            cost = gr_eval();
            lvl = cost;
            stall = 0;
            continue;
        }
        gr_backup();
        int moved = (rint_(2) == 0) ? gr_move_switch() : gr_move_fill();
        if (!moved) continue;
        long long c2 = gr_eval();
        long long delta = c2 - cost;
        int acc = (delta <= 0) || (urand() < exp(-(double)delta / GR_T));
        if (acc) cost = c2;
        else gr_restore();

        if (cost < lvl) {
            lvl = cost;
            stall = 0;
        } else {
            stall++;
        }
        if (stall > GR_STALL) {
            stall = 0;
            if (have) {
                gr_restore_best();
                cost = 0;
            } else {
                lvl = cost;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int n = bs_n;
    long long m = 0;
    for (int v = 0; v < n; v++)
        if (bs_side[v] == 0) m += bs_deg[v];
    printf("%d %lld\n", n, m);
    for (int v = 0; v < n; v++) {
        if (bs_side[v] != 0) continue;
        for (int k = 0; k < bs_deg[v]; k++)
            printf("%d %d\n", v, bs_adj[(size_t)v * (size_t)gr_d + (size_t)k]);
    }
    return 0;
}

/* ============================================================================ */

int main(int argc, char **argv) {
    if (argc > 6 && atoi(argv[6]) == 1) return grow_main(argc, argv);

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
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    /* Best near-miss (smallest raw cost, still above best_n) kept for ILS. */
    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;
    /* Consecutive failed fresh attempts; widens the group-order window. */
    long long fails = 0;

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
            /* Mostly K = 1 (bi-Cayley), sometimes K = 2. The window of
               candidate orders above best_n widens with consecutive failures. */
            K = (rint_(100) < 75) ? 1 : 2;
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 25 + 6;
            long long extra = fails / 40;
            if (extra > g0 / 10) extra = g0 / 10;
            span += extra;
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
        /* Polish threshold scales with the order so larger near-miss
           graphs also get the exhaustive coordinate sweep. */
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
            if (!from_near) fails++;
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
# Python glue: exact constructions, then bi-Cayley search, then growth from the
# best graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(3.0, min(0.92 * time_limit, time_limit - 6.0))
    deadline = start + total

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
        # Phase 1: bi-Cayley search, seeded with the best known order.
        rem = deadline - time.monotonic()
        t1 = 0.55 * rem
        if t1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best_n, 0],
                                timeout=t1 + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Phase 2: grow the best graph by subdivision with annealing repair.
        rem = deadline - time.monotonic() - 0.5
        if rem >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{rem:.2f}", 0, 1],
                                stdin_graph=best, timeout=rem + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
