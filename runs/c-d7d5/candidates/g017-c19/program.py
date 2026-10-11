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
# C engine 1: bi-Cayley search with breakout local search (clause weighting).
# Produces a valid base graph (the strongest known construction path here).
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
#define MT_LIMIT 2500

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

static int *g_mt = NULL;
static size_t g_mt_cap = 0;
static int g_mt_on = 0;

static int gmul_raw(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, d = y % GK;
    long long t = ((long long)a + (long long)gpow[b] * (long long)c) % GM;
    return (int)t * GK + (b + d) % GK;
}

static void set_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GG = m * k;
    long long p = 1 % m;
    for (int b = 0; b < k; b++) {
        gpow[b] = (int)p;
        p = (p * r) % m;
    }
    g_mt_on = 0;
    if (GG <= MT_LIMIT) {
        size_t need = (size_t)GG * (size_t)GG;
        if (need > g_mt_cap) {
            free(g_mt);
            g_mt = malloc(sizeof(int) * need);
            if (!g_mt) {
                fprintf(stderr, "out of memory\n");
                exit(1);
            }
            g_mt_cap = need;
        }
        for (int x = 0; x < GG; x++)
            for (int y = 0; y < GG; y++)
                g_mt[(size_t)x * (size_t)GG + (size_t)y] = gmul_raw(x, y);
        g_mt_on = 1;
    }
}

static inline int gmul(int x, int y) {
    if (g_mt_on) return g_mt[(size_t)x * (size_t)GG + (size_t)y];
    return gmul_raw(x, y);
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
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        int K = (rint_(100) < 75) ? 1 : 2;
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 25 + 6;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > 6000) continue;
        int N = 2 * K * GG;
        if (N <= best_n) continue;

        cur.K = K;
        cur.G = GG;
        ensure_cap(N);
        random_cfg(&cur);
        reset_weights(K, N);
        breakout(&cur, BREAK_ITERS);
        cost_of(&cur, 0);
        if (g_rawcost > 0 && g_rawcost <= POLISH_T) {
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
# C engine 2 (new construction): growth by vertex-pair insertion plus
# simulated annealing over degree-preserving double-edge swaps.
#
# Each step adds two vertices x (side A) and y (side B). Pick d edges
# (a_k, b_k) with distinct endpoints, rewire them to (a_k, y) and add
# (x, b_k). Degrees stay <= d and the graph stays bipartite. Then anneal
# with double-edge swaps minimising the number of ordered vertex pairs
# farther than D apart (computed with bitset ball expansion). A zero-cost
# state is a valid graph and becomes the new base for further growth.
# ----------------------------------------------------------------------------

GROW_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2600
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 64
#define MAXE (MAXN * MAXDEG / 2 + 2 * MAXDEG)

typedef struct {
    int n, m;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int ea[MAXE], eb[MAXE];
} State;

static State cur, best, work;
static uint64_t RA[MAXN][MAXW], RB[MAXN][MAXW];
static int D = 3, dgr = 3;
static double deadline = 0.0;
static uint64_t rs = 88172645463325252ULL;
static int tu[MAXE], tv[MAXE], perm[MAXE];
static int usedA[MAXN], usedB[MAXN], stampc = 0;
static int col_[MAXN], qbuf[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd_unit(void) {
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

static int adj_has(const State *s, int v, int u) {
    for (int k = 0; k < s->deg[v]; k++)
        if (s->adj[v][k] == u) return 1;
    return 0;
}

static void adj_replace(State *s, int v, int old, int nw) {
    for (int k = 0; k < s->deg[v]; k++) {
        if (s->adj[v][k] == old) {
            s->adj[v][k] = nw;
            return;
        }
    }
}

/* Double-edge swap: edges k1=(a1,b1), k2=(a2,b2) become (a1,b2), (a2,b1).
   Calling it twice on the same pair restores the original state. */
static void do_swap(State *s, int k1, int k2) {
    int a1 = s->ea[k1], b1 = s->eb[k1], a2 = s->ea[k2], b2 = s->eb[k2];
    adj_replace(s, a1, b1, b2);
    adj_replace(s, b1, a1, a2);
    adj_replace(s, a2, b2, b1);
    adj_replace(s, b2, a2, a1);
    s->eb[k1] = b2;
    s->eb[k2] = b1;
}

/* Returns the number of ordered vertex pairs at distance > D (0 means valid). */
static long long eval_bad(const State *s) {
    int n = s->n, W = (n + 63) / 64;
    uint64_t (*P)[MAXW] = RA, (*Q)[MAXW] = RB, (*T)[MAXW];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) P[v][w] = 0;
        P[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) Q[v][w] = P[v][w];
            for (int k = 0; k < s->deg[v]; k++) {
                const uint64_t *src = P[s->adj[v][k]];
                for (int w = 0; w < W; w++) Q[v][w] |= src[w];
            }
        }
        T = P;
        P = Q;
        Q = T;
    }
    long long reached = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < W; w++)
            reached += pc64(P[v][w]);
    return (long long)n * (long long)n - reached;
}

/* Adds two vertices x (side A, id n) and y (side B, id n+1), each of degree dgr. */
static int grow_pair(State *s) {
    int m = s->m, d = dgr;
    if (s->n + 2 > MAXN || m + d > MAXE || m < d) return 0;
    for (int i = 0; i < m; i++) perm[i] = i;
    for (int i = m - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = perm[i];
        perm[i] = perm[j];
        perm[j] = t;
    }
    stampc++;
    int chosen[MAXDEG], cnt = 0;
    for (int t = 0; t < m && cnt < d; t++) {
        int e = perm[t];
        int a = s->ea[e], b = s->eb[e];
        if (usedA[a] == stampc || usedB[b] == stampc) continue;
        usedA[a] = stampc;
        usedB[b] = stampc;
        chosen[cnt++] = e;
    }
    if (cnt < d) return 0;

    int x = s->n, y = s->n + 1;
    s->deg[x] = 0;
    s->deg[y] = 0;
    s->n += 2;
    for (int k = 0; k < d; k++) {
        int e = chosen[k];
        int a = s->ea[e], b = s->eb[e];
        adj_replace(s, a, b, y);
        adj_replace(s, b, a, x);
        s->eb[e] = y;
        s->adj[y][s->deg[y]++] = a;
        s->adj[x][s->deg[x]++] = b;
        s->ea[m + k] = x;
        s->eb[m + k] = b;
    }
    s->m = m + d;
    return 1;
}

/* Simulated annealing on double-edge swaps. Returns 1 when the state becomes valid. */
static int anneal(State *s, long iters, double T0, double T1) {
    long long cc = eval_bad(s);
    if (cc == 0) return 1;
    for (long it = 0; it < iters; it++) {
        if ((it & 15) == 0 && now_s() > deadline) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int k1 = rnd_int(s->m), k2 = rnd_int(s->m);
        if (k1 == k2) continue;
        int a1 = s->ea[k1], b1 = s->eb[k1], a2 = s->ea[k2], b2 = s->eb[k2];
        if (a1 == a2 || b1 == b2) continue;
        if (adj_has(s, a1, b2) || adj_has(s, a2, b1)) continue;
        do_swap(s, k1, k2);
        long long nc = eval_bad(s);
        long long delta = nc - cc;
        if (delta <= 0 || rnd_unit() < exp(-(double)delta / T)) {
            cc = nc;
            if (cc == 0) return 1;
        } else {
            do_swap(s, k1, k2);
        }
    }
    return cc == 0;
}

static int read_graph(State *s) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0 || m > MAXE - MAXDEG) return 0;
    for (int v = 0; v < n; v++) s->deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (s->deg[u] >= dgr || s->deg[v] >= dgr) return 0;
        s->adj[u][s->deg[u]++] = v;
        s->adj[v][s->deg[v]++] = u;
        tu[i] = u;
        tv[i] = v;
    }
    for (int v = 0; v < n; v++) col_[v] = -1;
    for (int s0 = 0; s0 < n; s0++) {
        if (col_[s0] != -1) continue;
        col_[s0] = 0;
        int head = 0, tail = 0;
        qbuf[tail++] = s0;
        while (head < tail) {
            int u = qbuf[head++];
            for (int k = 0; k < s->deg[u]; k++) {
                int v = s->adj[u][k];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    qbuf[tail++] = v;
                } else if (col_[v] == col_[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < m; i++) {
        int u = tu[i], v = tv[i];
        if (col_[u] == 0) {
            s->ea[i] = u;
            s->eb[i] = v;
        } else {
            s->ea[i] = v;
            s->eb[i] = u;
        }
    }
    s->n = n;
    s->m = m;
    return 1;
}

int main(int argc, char **argv) {
    dgr = argc > 1 ? atoi(argv[1]) : 3;
    D = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 5.0;

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    deadline = now_s() + tl;
    if (dgr < 1 || dgr > MAXDEG - 2 || D < 1 || !read_graph(&cur)) {
        printf("0 0\n");
        return 0;
    }
    if (eval_bad(&cur) != 0) {
        printf("0 0\n");
        return 0;
    }
    best = cur;

    int fails = 0;
    while (now_s() < deadline) {
        long stage = 3000 + 300L * (long)(fails < 20 ? fails : 20);
        work = best;
        if (!grow_pair(&work)) break;
        if (anneal(&work, stage, 2.0, 0.05)) {
            best = work;
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", best.n, best.m);
    for (int k = 0; k < best.m; k++)
        printf("%d %d\n", best.ea[k], best.eb[k]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, bi-Cayley base search, then growth search.
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
        # Phase 1: bi-Cayley base search (lifts over small groups).
        remaining = deadline - time.monotonic()
        c1 = 0.6 * remaining - 1.0
        if c1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c1:.2f}", best_n],
                                timeout=c1 + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Phase 2 (new construction): grow the best base by vertex pairs and
        # repair with annealing over degree-preserving edge swaps.
        remaining = deadline - time.monotonic()
        c2 = remaining - 1.0
        if c2 >= 3.0:
            try:
                out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{c2:.2f}"],
                                stdin_graph=best, timeout=c2 + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
