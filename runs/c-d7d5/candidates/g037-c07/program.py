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
# PARENT C engine (bi-Cayley breakout search, polish, near-miss ILS).
# Used for every case except d=7, D=5, and as the start-graph generator
# for the target case.
# ----------------------------------------------------------------------------

PARENT_C_SOURCE = r'''
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
# NEW C engine for the target (d=7, D=5): grow-and-anneal on general bipartite
# graphs. Starting from a valid graph, it adds one A-vertex and one B-vertex
# (each of degree d, by splicing d existing edges), then runs simulated
# annealing with degree-preserving 2-switches. Cost = number of vertex pairs
# at distance > D, computed exactly with bitset balls. On success the graph is
# saved and the grow step repeats; on failure it restarts from the best graph.
# ----------------------------------------------------------------------------

GROW_C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2600
#define DMAX 16
#define MAXE (MAXN * DMAX)
#define MAXW ((MAXN + 63) / 64)

typedef struct {
    int nv, m;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][DMAX];
    int ea[MAXE], eb[MAXE];   /* edge e joins A-end ea[e] (col 0) and B-end eb[e] (col 1) */
} State;

static State cur, best;
static int Dd = 7, DD = 5;
static uint64_t rs = 88172645463325252ULL;
static int curstamp = 0;
static int tch[MAXE];
static int usedV[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double rnd01(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Replace neighbour old by nw in adj[v] (exactly one occurrence). */
static void rep(int v, int old, int nw) {
    int dg = cur.deg[v];
    for (int t = 0; t < dg; t++) {
        if (cur.adj[v][t] == old) {
            cur.adj[v][t] = nw;
            return;
        }
    }
}

static int has_edge(int a, int b) {
    int dg = cur.deg[a];
    for (int t = 0; t < dg; t++)
        if (cur.adj[a][t] == b) return 1;
    return 0;
}

/* Currently edges (a1,b1) at e1 and (a2,b2) at e2; afterwards (a1,b2) at e1 and (a2,b1) at e2. */
static void apply_switch(int e1, int e2, int a1, int b1, int a2, int b2) {
    rep(a1, b1, b2);
    rep(b1, a1, a2);
    rep(a2, b2, b1);
    rep(b2, a2, a1);
    cur.ea[e1] = a1;
    cur.eb[e1] = b2;
    cur.ea[e2] = a2;
    cur.eb[e2] = b1;
}

/* Number of unordered vertex pairs at distance > DD in the current graph. */
static long long cost_full(void) {
    int N = cur.nv, W = (N + 63) / 64;
    uint64_t *A = RA, *B = RB;
    memset(A, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        A[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int s = 0; s < DD; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = B + (size_t)v * W;
            const uint64_t *src = A + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            int dg = cur.deg[v];
            for (int t = 0; t < dg; t++) {
                const uint64_t *su = A + (size_t)cur.adj[v][t] * W;
                for (int w = 0; w < W; w++) dst[w] |= su[w];
            }
        }
        uint64_t *tmp = A;
        A = B;
        B = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *row = A + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(row[w]);
        bad += N - cnt;
    }
    return bad / 2;
}

/* Add two vertices x (side A) and y (side B), each of degree Dd, by splicing
   Dd edges (a,b): remove (a,b), add (a,y) and (x,b). Degrees of old vertices
   are unchanged. Returns the number of splices done. */
static int grow(void) {
    if (cur.nv + 2 > MAXN) return 0;
    curstamp++;
    int x = cur.nv, y = cur.nv + 1;
    cur.col[x] = 0;
    cur.col[y] = 1;
    cur.deg[x] = 0;
    cur.deg[y] = 0;
    cur.nv += 2;
    int m0 = cur.m, cnt = 0;
    long tries = 0;
    while (cnt < Dd && tries < 2000000) {
        tries++;
        int e = (int)(rnd() % (uint64_t)m0);
        if (tch[e] == curstamp) continue;
        int a = cur.ea[e], b = cur.eb[e];
        if (usedV[a] == curstamp || usedV[b] == curstamp) continue;
        tch[e] = curstamp;
        usedV[a] = curstamp;
        usedV[b] = curstamp;
        rep(a, b, y);
        rep(b, a, x);
        cur.ea[e] = a;
        cur.eb[e] = y;
        cur.ea[cur.m] = x;
        cur.eb[cur.m] = b;
        cur.m++;
        cur.adj[x][cur.deg[x]++] = b;
        cur.adj[y][cur.deg[y]++] = a;
        cnt++;
    }
    return cnt;
}

/* Read "n m" and edges from stdin; orient edges A->B by a BFS 2-colouring.
   Returns 0 on any malformed or non-bipartite input. */
static int load_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 2 || m < 0 || m > MAXE) return 0;
    cur.nv = n;
    memset(cur.deg, 0, sizeof(cur.deg));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (cur.deg[u] >= Dd || cur.deg[v] >= Dd) return 0;
        if (has_edge(u, v)) return 0;
        cur.adj[u][cur.deg[u]++] = v;
        cur.adj[v][cur.deg[v]++] = u;
        cur.ea[i] = u;
        cur.eb[i] = v;
    }
    cur.m = m;
    for (int v = 0; v < n; v++) cur.col[v] = -1;
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (cur.col[s] != -1) continue;
        cur.col[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int t = 0; t < cur.deg[u]; t++) {
                int w = cur.adj[u][t];
                if (cur.col[w] == -1) {
                    cur.col[w] = 1 - cur.col[u];
                    queue[tail++] = w;
                } else if (cur.col[w] == cur.col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int e = 0; e < m; e++) {
        if (cur.col[cur.ea[e]] != 0) {
            int t = cur.ea[e];
            cur.ea[e] = cur.eb[e];
            cur.eb[e] = t;
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    double seg = argc > 5 ? atof(argv[5]) : 3.0;

    if (Dd < 1 || Dd > DMAX || DD < 1 || seg <= 0.0) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    if (!load_graph() || cost_full() != 0) {
        printf("0 0\n");
        return 0;
    }
    best = cur;

    const double T0 = 3.0, TEND = 0.2;
    double deadline = now_s() + tl;
    while (now_s() < deadline) {
        cur = best;
        grow();
        double seg_start = now_s();
        double seg_end = seg_start + seg;
        if (seg_end > deadline) seg_end = deadline;
        long long c = cost_full();
        while (c > 0) {
            double t = now_s();
            if (t >= seg_end) break;
            double frac = (t - seg_start) / seg;
            if (frac > 1.0) frac = 1.0;
            double T = T0 * pow(TEND / T0, frac);

            int e1 = (int)(rnd() % (uint64_t)cur.m);
            int e2 = (int)(rnd() % (uint64_t)cur.m);
            if (e1 == e2) continue;
            int a1 = cur.ea[e1], b1 = cur.eb[e1];
            int a2 = cur.ea[e2], b2 = cur.eb[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;

            apply_switch(e1, e2, a1, b1, a2, b2);
            long long c2 = cost_full();
            long long dlt = c2 - c;
            if (dlt <= 0 || rnd01() < exp(-(double)dlt / T)) {
                c = c2;
            } else {
                apply_switch(e1, e2, a1, b2, a2, b1);
            }
        }
        if (c == 0) best = cur;
    }

    printf("%d %d\n", best.nv, best.m);
    for (int e = 0; e < best.m; e++)
        printf("%d %d\n", best.ea[e], best.eb[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.88 * time_limit, time_limit - 5.0))
    hard = start + time_limit - 2.0

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

    if d == 7 and D == 5:
        # Target case: parent bi-Cayley search for a strong start graph, then
        # grow-and-anneal on general bipartite graphs from the best graph.
        p_budget = 0.6 * (deadline - time.monotonic())
        if p_budget >= 2.0:
            try:
                out = lib.run_c(PARENT_C_SOURCE, [d, D, seed, f"{p_budget:.2f}", best_n],
                                timeout=max(1.0, hard - time.monotonic()))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass
        g_budget = deadline - time.monotonic() - 1.0
        if g_budget >= 2.0:
            seg = max(1.5, g_budget / 6.0)
            try:
                out = lib.run_c(GROW_C_SOURCE, [d, D, seed, f"{g_budget:.2f}", f"{seg:.2f}"],
                                stdin_graph=best, timeout=max(1.0, hard - time.monotonic()))
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass
    else:
        # Breakout search plus polish and near-miss ILS in C, seeded with the best
        # known order as a lower bound.
        if d >= 3 and D >= 3:
            c_budget = deadline - time.monotonic() - 1.5
            if c_budget >= 2.0:
                try:
                    out = lib.run_c(PARENT_C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                    timeout=time_limit - 3.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
