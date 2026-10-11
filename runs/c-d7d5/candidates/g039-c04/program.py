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
# Stage 1 C engine: bi-Cayley search with breakout local search (clause
# weighting), a unit-weight coordinate polish for near-solutions, and iterated
# local search on near-misses.
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
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;
    long long fails = 0;

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
# Stage 2 C engine (new): simulated annealing over general bipartite graphs.
#
# State: any bipartite graph with max degree d (side 0 = first half of the
# vertices, side 1 = second half). Moves: degree-preserving 2-switches,
# deficit transfers, and additions of missing edges (which never increase
# the number of far pairs). Cost = number of unordered vertex pairs at
# distance > D, computed exactly with bitset BFS. When cost reaches 0 the
# graph is saved and grown by one A-vertex and one B-vertex, which the
# annealing then repairs. On repeated failure it restarts from the best
# saved valid graph. Output is always the best valid graph found.
# ----------------------------------------------------------------------------

ANNEAL_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXGROW 400
#define STAGE_IT 3000
#define T_START 1.2
#define T_END 0.15

static int Dd = 3, DD = 3;
static int N = 0, CAP = 0, WCAP = 0;
static int *side_ = NULL, *deg = NULL, *adj = NULL;
static int *bdeg = NULL, *badj = NULL;
static int bestN = 0, have_best = 0;
static uint64_t *rb = NULL, *rb2 = NULL;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double urand(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int x, int y) {
    int dx = deg[x];
    for (int k = 0; k < dx; k++)
        if (adj[x * Dd + k] == y) return 1;
    return 0;
}

static void half_del(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (adj[x * Dd + k] == y) {
            adj[x * Dd + k] = adj[x * Dd + deg[x] - 1];
            deg[x]--;
            return;
        }
    }
}

static void add_edge(int x, int y) {
    adj[x * Dd + deg[x]++] = y;
    adj[y * Dd + deg[y]++] = x;
}

static void del_edge(int x, int y) {
    half_del(x, y);
    half_del(y, x);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD. */
static long long badcost(void) {
    int W = (N + 63) >> 6;
    uint64_t *cur = rb, *nxt = rb2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[v * Dd + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *src = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(src[w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Random vertex on side s with at least one edge, or -1. */
static int pick_side(int s) {
    for (int t = 0; t < 60; t++) {
        int v = rint_(N);
        if (side_[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* 2-switch: edges (x,p),(y,q) become (x,q),(y,p). Side-0 vertices x, y. */
static int mv_switch(int *a1, int *b1, int *a2, int *b2) {
    int x = pick_side(0), y = pick_side(0);
    if (x < 0 || y < 0 || x == y) return 0;
    int p = adj[x * Dd + rint_(deg[x])];
    int q = adj[y * Dd + rint_(deg[y])];
    if (p == q || has_edge(x, q) || has_edge(y, p)) return 0;
    del_edge(x, p);
    del_edge(y, q);
    add_edge(x, q);
    add_edge(y, p);
    *a1 = x; *b1 = p; *a2 = y; *b2 = q;
    return 1;
}

/* Deficient p takes a new neighbour y; y's old neighbour x loses it. */
static int mv_transfer(int *pp, int *xx, int *yy) {
    int p = -1;
    for (int t = 0; t < 60; t++) {
        int v = rint_(N);
        if (deg[v] < Dd) { p = v; break; }
    }
    if (p < 0) return 0;
    int y = pick_side(1 - side_[p]);
    if (y < 0) return 0;
    int x = adj[y * Dd + rint_(deg[y])];
    if (x == p || has_edge(p, y)) return 0;
    del_edge(x, y);
    add_edge(p, y);
    *pp = p; *xx = x; *yy = y;
    return 1;
}

/* Add a missing edge between two deficient vertices on opposite sides. */
static int mv_add(int *pp, int *qq) {
    for (int t = 0; t < 80; t++) {
        int v = rint_(N);
        if (deg[v] >= Dd) continue;
        int w = rint_(N);
        if (side_[w] == side_[v] || deg[w] >= Dd || has_edge(v, w)) continue;
        add_edge(v, w);
        *pp = v; *qq = w;
        return 1;
    }
    return 0;
}

static void fill_greedy(void) {
    for (int t = 0; t < N * 20; t++) {
        int a, b;
        (void)mv_add(&a, &b);
    }
}

static void save_best(void) {
    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * (size_t)Dd);
    have_best = 1;
}

static void restore_best(long long *cur) {
    N = bestN;
    memcpy(deg, bdeg, sizeof(int) * (size_t)N);
    memcpy(adj, badj, sizeof(int) * (size_t)N * (size_t)Dd);
    *cur = 0;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    if (Dd < 1 || Dd > 64 || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    double t0 = now_s();
    deadline = t0 + tl;

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    CAP = n0 + 2 * MAXGROW + 4;
    WCAP = (CAP + 63) >> 6;
    side_ = malloc(sizeof(int) * (size_t)CAP);
    deg = calloc((size_t)CAP, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)CAP * (size_t)Dd);
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = malloc(sizeof(int) * (size_t)CAP * (size_t)Dd);
    rb = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    rb2 = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)WCAP);
    if (!side_ || !deg || !adj || !bdeg || !badj || !rb || !rb2) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int v = 0; v < N; v++) side_[v] = (v < n0 / 2) ? 0 : 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || side_[u] == side_[v] ||
            deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    long long cur = badcost();
    int stage = 0;
    double T = T_START;

    while (now_s() < deadline) {
        if (cur == 0) {
            save_best();
            if (N - n0 >= 2 * MAXGROW || N + 2 > CAP) break;
            N += 2;
            side_[N - 2] = 0;
            side_[N - 1] = 1;
            deg[N - 2] = 0;
            deg[N - 1] = 0;
            fill_greedy();
            cur = badcost();
            stage = 0;
            continue;
        }
        if (stage >= STAGE_IT) {
            stage = 0;
            if (have_best) restore_best(&cur);
            continue;
        }

        stage++;
        double frac = (double)stage / (double)STAGE_IT;
        T = T_START * pow(T_END / T_START, frac);

        int mt = rint_(10);
        int type = 0, applied = 0;
        int A1 = 0, B1 = 0, A2 = 0, B2 = 0;
        if (mt < 4) {
            type = 1;
            applied = mv_switch(&A1, &B1, &A2, &B2);
        } else if (mt < 8) {
            type = 2;
            applied = mv_transfer(&A1, &B1, &A2);
        } else {
            type = 3;
            applied = mv_add(&A1, &B1);
        }
        if (!applied) continue;

        long long nc = badcost();
        long long delta = nc - cur;
        if (delta <= 0 || urand() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (type == 1) {
                /* applied: (A1,B2),(A2,B1) added; (A1,B1),(A2,B2) removed */
                del_edge(A1, B2);
                del_edge(A2, B1);
                add_edge(A1, B1);
                add_edge(A2, B2);
            } else if (type == 2) {
                /* applied: (B1,A2) removed, (A1,A2) added */
                del_edge(A1, A2);
                add_edge(B1, A2);
            } else {
                del_edge(A1, B1);
            }
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bdeg[v];
    m2 /= 2;
    printf("%d %lld\n", bestN, m2);
    for (int v = 0; v < bestN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * Dd + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then bi-Cayley search, then annealing
# with vertex growth on the best graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 8.0))

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
        # Stage 1: bi-Cayley search (60% of the remaining budget).
        remaining = deadline - time.monotonic()
        t1 = 0.60 * remaining
        if t1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best_n],
                                timeout=t1 + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: annealing with vertex growth, started from the best graph.
        remaining = deadline - time.monotonic()
        if remaining >= 2.0:
            try:
                out = lib.run_c(ANNEAL_SOURCE, [d, D, seed + 1, f"{remaining - 0.5:.2f}"],
                                stdin_graph=best, timeout=remaining + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
