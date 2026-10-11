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
#
# Stage 1 (bi-Cayley search): breakout local search over Z_m x| Z_k lifts with
# clause weighting, coordinate polish, and near-miss ILS (as in the parent).
#
# Stage 2 (NEW: insertion + annealed repair on the explicit graph):
#   The best bi-Cayley graph is d-regular. To add two vertices x (side A) and
#   y (side B), pick d-1 pairwise vertex-disjoint edges (a_k, b_k), delete them,
#   and join a_k-y, b_k-x, plus the edge x-y. Degrees stay exactly d, the graph
#   stays bipartite and simple, and the order grows by 2. The insertion usually
#   breaks some distance-D pairs, so simulated annealing repairs it. Moves are
#   degree-preserving double-edge switches. The cost is the number of vertex
#   pairs at distance > D, computed exactly with bitset ball expansion (about a
#   millisecond at n around 1100). A state with cost 0 is a valid graph, so
#   every accepted growth step is exactly valid.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h, dart (l, i) joins
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
#define SEARCH_FRAC 0.5
#define AUG_END_FRAC 0.9
#define AUG_EXTRA 400
#define AUG_MAXN 5000

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

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

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
            cost_of(c, 1);
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

/* ------------------------------------------------------------------------
   Augmentation on an explicit d-regular bipartite graph.
   ------------------------------------------------------------------------ */

typedef struct {
    int n, m, cap_n, cap_m;
    int *adj;   /* adj[v*Dd + t] */
    int *side;  /* 0 = A, 1 = B */
    int *E;     /* E[2e] is in A, E[2e+1] is in B */
} Gr;

static void gr_alloc(Gr *g, int cap_n) {
    g->n = 0;
    g->m = 0;
    g->cap_n = cap_n;
    g->cap_m = cap_n * Dd;
    g->adj = malloc(sizeof(int) * (size_t)cap_n * (size_t)Dd);
    g->side = malloc(sizeof(int) * (size_t)cap_n);
    g->E = malloc(sizeof(int) * 2 * (size_t)g->cap_m);
    if (!g->adj || !g->side || !g->E) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static void gr_copy(Gr *dst, const Gr *src) {
    dst->n = src->n;
    dst->m = src->m;
    memcpy(dst->adj, src->adj, sizeof(int) * (size_t)src->n * (size_t)Dd);
    memcpy(dst->side, src->side, sizeof(int) * (size_t)src->n);
    memcpy(dst->E, src->E, sizeof(int) * 2 * (size_t)src->m);
}

static void replace_nb(Gr *g, int v, int old, int nw) {
    int *p = g->adj + (size_t)v * Dd;
    for (int t = 0; t < Dd; t++) {
        if (p[t] == old) {
            p[t] = nw;
            return;
        }
    }
    fprintf(stderr, "internal: neighbour not found\n");
    exit(1);
}

static int is_adj(const Gr *g, int u, int v) {
    const int *p = g->adj + (size_t)u * Dd;
    for (int t = 0; t < Dd; t++)
        if (p[t] == v) return 1;
    return 0;
}

/* Double-edge switch of edges i and j: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
   Applying it twice restores the original graph. */
static void sw(Gr *g, int i, int j) {
    int a1 = g->E[2 * i], b1 = g->E[2 * i + 1];
    int a2 = g->E[2 * j], b2 = g->E[2 * j + 1];
    replace_nb(g, a1, b1, b2);
    replace_nb(g, b2, a2, a1);
    replace_nb(g, a2, b2, b1);
    replace_nb(g, b1, a1, a2);
    g->E[2 * i + 1] = b2;
    g->E[2 * j] = a2;
    g->E[2 * j + 1] = b1;
}

static int can_sw(const Gr *g, int i, int j) {
    int a1 = g->E[2 * i], b1 = g->E[2 * i + 1];
    int a2 = g->E[2 * j], b2 = g->E[2 * j + 1];
    if (a1 == a2 || b1 == b2) return 0;
    if (is_adj(g, a1, b2) || is_adj(g, a2, b1)) return 0;
    return 1;
}

static int *ua = NULL, *ub = NULL, ustamp = 0;
static uint64_t *bufA = NULL, *bufB = NULL;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DD, via bitset ball expansion. */
static long long ball_bad(const Gr *g) {
    int n = g->n;
    size_t W = (size_t)((n + 63) >> 6);
    size_t need = (size_t)n * W;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * need);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *row = nxt + (size_t)v * W;
            memcpy(row, cur + (size_t)v * W, sizeof(uint64_t) * W);
            const int *p = g->adj + (size_t)v * Dd;
            for (int t = 0; t < Dd; t++) {
                const uint64_t *src = cur + (size_t)p[t] * W;
                for (size_t w = 0; w < W; w++) row[w] |= src[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long missing = 0;
    for (int v = 0; v < n; v++) {
        long long pc = 0;
        const uint64_t *row = cur + (size_t)v * W;
        for (size_t w = 0; w < W; w++) pc += popc64(row[w]);
        missing += (long long)n - pc;
    }
    return missing / 2;
}

/* Remove d-1 pairwise disjoint edges (a_k,b_k); add x (side A), y (side B),
   edges a_k-y, b_k-x, and x-y. Degrees stay d; order grows by 2. */
static int insert2(Gr *g) {
    int d = Dd;
    int ch[MAXD], as[MAXD], bs[MAXD];
    int nc = 0;
    ustamp++;
    for (int tries = 0; tries < 20000 && nc < d - 1; tries++) {
        int e = rint_(g->m);
        int a = g->E[2 * e], b = g->E[2 * e + 1];
        if (ua[a] == ustamp || ub[b] == ustamp) continue;
        ua[a] = ustamp;
        ub[b] = ustamp;
        ch[nc++] = e;
    }
    if (nc < d - 1) return 0;
    int x = g->n, y = g->n + 1;
    for (int k = 0; k < nc; k++) {
        as[k] = g->E[2 * ch[k]];
        bs[k] = g->E[2 * ch[k] + 1];
    }
    for (int k = 0; k < nc; k++) {
        replace_nb(g, as[k], bs[k], y);
        replace_nb(g, bs[k], as[k], x);
        g->E[2 * ch[k] + 1] = y;
    }
    for (int k = 0; k < nc; k++) {
        g->E[2 * g->m] = x;
        g->E[2 * g->m + 1] = bs[k];
        g->m++;
    }
    g->E[2 * g->m] = x;
    g->E[2 * g->m + 1] = y;
    g->m++;
    g->side[x] = 0;
    g->side[y] = 1;
    int *px = g->adj + (size_t)x * Dd;
    int *py = g->adj + (size_t)y * Dd;
    for (int k = 0; k < d - 1; k++) {
        px[k] = bs[k];
        py[k] = as[k];
    }
    px[d - 1] = y;
    py[d - 1] = x;
    g->n += 2;
    return 1;
}

/* Annealing on double-edge switches, cost = bad pairs. Returns 1 when cost 0
   is reached (g is then a valid graph). Otherwise g holds an arbitrary state. */
static int anneal(Gr *g, double t_end, double T0, double T1) {
    double t_start = now_s();
    double span = t_end - t_start;
    if (span < 1e-3) span = 1e-3;
    long long cost = ball_bad(g);
    if (cost == 0) return 1;
    double T = T0;
    long long it = 0;
    for (;;) {
        it++;
        if ((it & 7) == 1) {
            double t = now_s();
            if (t >= t_end) break;
            double f = (t - t_start) / span;
            if (f > 1.0) f = 1.0;
            T = T0 * pow(T1 / T0, f);
        }
        int i = rint_(g->m), j = rint_(g->m);
        if (i == j || !can_sw(g, i, j)) continue;
        sw(g, i, j);
        long long nc = ball_bad(g);
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) return 1;
        } else {
            sw(g, i, j);
        }
    }
    return 0;
}

/* Grow the best valid graph by 2 vertices at a time. Each stage inserts into a
   copy of the best graph and anneals it back to validity. */
static void augment(Gr *best, double t_end) {
    int cap_n = best->cap_n;
    Gr work;
    gr_alloc(&work, cap_n);
    ua = calloc((size_t)cap_n, sizeof(int));
    ub = calloc((size_t)cap_n, sizeof(int));
    size_t W = (size_t)((cap_n + 63) / 64);
    bufA = malloc(sizeof(uint64_t) * (size_t)cap_n * W);
    bufB = malloc(sizeof(uint64_t) * (size_t)cap_n * W);
    if (!ua || !ub || !bufA || !bufB) return;
    for (;;) {
        double now = now_s();
        double remain = t_end - now;
        if (remain < 0.2) break;
        if (best->n + 2 > cap_n) break;
        double slen = remain / 3.0;
        if (slen < 0.5) slen = remain;
        gr_copy(&work, best);
        if (!insert2(&work)) continue;
        if (anneal(&work, now + slen, 1.0, 0.08)) gr_copy(best, &work);
    }
}

/* Explicit graph from a bi-Cayley configuration. Needs set_group first. */
static int build_from_cfg(Gr *g, const Cfg *c) {
    int K = c->K, G = c->G, n = 2 * K * G;
    int *cnt = calloc((size_t)n, sizeof(int));
    if (!cnt) return 0;
    g->n = n;
    g->m = 0;
    for (int v = 0; v < n; v++) g->side[v] = (v >= K * G);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int gg = 0; gg < G; gg++) {
                int a = i * G + gg;
                int b = (K + j) * G + gmul(gg, s);
                if (cnt[a] >= Dd || cnt[b] >= Dd) {
                    free(cnt);
                    return 0;
                }
                g->E[2 * g->m] = a;
                g->E[2 * g->m + 1] = b;
                g->m++;
                g->adj[(size_t)a * Dd + cnt[a]++] = b;
                g->adj[(size_t)b * Dd + cnt[b]++] = a;
            }
        }
    }
    free(cnt);
    return 1;
}

static void print_graph(const Gr *g) {
    printf("%d %d\n", g->n, g->m);
    for (int e = 0; e < g->m; e++) printf("%d %d\n", g->E[2 * e], g->E[2 * e + 1]);
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
    double search_end = t0 + tl * SEARCH_FRAC;
    double aug_end = t0 + tl * AUG_END_FRAC;
    deadline = search_end;
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    int fails = 0;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;

    while (now_s() < deadline) {
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
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
    Gr base;
    gr_alloc(&base, best_cfg.K * best_cfg.G * 2 + AUG_EXTRA);
    if (!build_from_cfg(&base, &best_cfg)) {
        printf("0 0\n");
        return 0;
    }
    if (base.n <= AUG_MAXN) augment(&base, aug_end);
    print_graph(&base);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search and augmentation.
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

    # C: bi-Cayley search for the first half of its budget, then insertion
    # augmentation with annealed repair on the best regular graph it found.
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
