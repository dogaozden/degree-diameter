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
# Stage 1 C engine (unchanged from parent): bi-Cayley search with breakout
# local search (clause weighting) and a unit-weight coordinate polish.
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
    Cfg cur, best_cfg;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));

    while (now_s() < deadline) {
        /* Mostly K = 1 (bi-Cayley), sometimes K = 2. */
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
# Stage 2 C engine (new): grow an explicit bipartite graph by vertex pairs.
#
# Each growth step adds one A vertex and one B vertex with degree 0. Then a
# simulated-annealing repair works on the explicit graph with degree <= d:
#   - 2-switch (degree preserving) between random edges,
#   - transfer: move one end of an edge onto a deficient vertex,
#   - greedy addition of edges between deficient A and B vertices.
# Cost = number of unordered vertex pairs at distance > D (0 means valid).
# Distances are computed with bitset balls. The best valid graph is printed.
# ----------------------------------------------------------------------------

GROW_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DMAX 64
#define GROW_STAGE 3000
#define EXTRA 600
#define NMAXIN 4000

static int dd = 3, DD = 3;
static int N = 0, CAP = 0, W = 1;
static int *side, *deg, *adj, *bdeg, *badj, *sdeg, *sadj, *defA, *defB;
static uint64_t *bufA, *bufB;
static int bestN = 0;
static long long cur_cost = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rfloat(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int is_adj(int a, int b) {
    const int *p = adj + (size_t)a * DMAX;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void push_nb(int a, int b) {
    adj[(size_t)a * DMAX + deg[a]] = b;
    deg[a]++;
}

static void remove_nb(int a, int b) {
    int *p = adj + (size_t)a * DMAX;
    for (int k = 0; k < deg[a]; k++) {
        if (p[k] == b) {
            p[k] = p[deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    push_nb(a, b);
    push_nb(b, a);
}

static void del_edge(int a, int b) {
    remove_nb(a, b);
    remove_nb(b, a);
}

/* Number of unordered pairs at distance > DD (including disconnected). */
static long long cost(void) {
    uint64_t *cur = bufA, *nxt = bufB;
    size_t tot = (size_t)N * (size_t)W;
    memset(cur, 0, sizeof(uint64_t) * tot);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            const int *p = adj + (size_t)v * DMAX;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *nb = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *src = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(src[w]);
        miss += (long long)(N - c);
    }
    return miss / 2;
}

static void save_state(void) {
    memcpy(sdeg, deg, sizeof(int) * (size_t)N);
    memcpy(sadj, adj, sizeof(int) * (size_t)N * DMAX);
}

static void restore_state(void) {
    memcpy(deg, sdeg, sizeof(int) * (size_t)N);
    memcpy(adj, sadj, sizeof(int) * (size_t)N * DMAX);
}

static void record_best(void) {
    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * DMAX);
}

static int rand_side(int s) {
    for (;;) {
        int v = rint_(N);
        if (side[v] == s) return v;
    }
}

static void greedy_add(void) {
    int nda = 0, ndb = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= dd) continue;
        if (side[v] == 0) defA[nda++] = v;
        else defB[ndb++] = v;
    }
    for (int i = 0; i < nda; i++) {
        int a = defA[i];
        int off = ndb > 0 ? rint_(ndb) : 0;
        for (int jj = 0; jj < ndb && deg[a] < dd; jj++) {
            int j = (jj + off) % ndb;
            int b = defB[j];
            if (deg[b] < dd && !is_adj(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving 2-switch on two random edges. */
static int move_switch(void) {
    int a1 = rand_side(0), a2 = rand_side(0);
    if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) return 0;
    int b1 = adj[(size_t)a1 * DMAX + rint_(deg[a1])];
    int b2 = adj[(size_t)a2 * DMAX + rint_(deg[a2])];
    if (b1 == b2 || is_adj(a1, b2) || is_adj(a2, b1)) return 0;
    del_edge(a1, b1);
    del_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    return 1;
}

/* Move one end of a random edge onto the deficient vertex v. */
static int move_transfer(int v) {
    if (side[v] == 1) {
        int a = rand_side(0);
        if (deg[a] == 0) return 0;
        int b = adj[(size_t)a * DMAX + rint_(deg[a])];
        if (b == v || is_adj(a, v)) return 0;
        del_edge(a, b);
        add_edge(a, v);
        return 1;
    } else {
        int b = rand_side(1);
        if (deg[b] == 0) return 0;
        int a = adj[(size_t)b * DMAX + rint_(deg[b])];
        if (a == v || is_adj(v, b)) return 0;
        del_edge(a, b);
        add_edge(v, b);
        return 1;
    }
}

static void step(double T) {
    int nda = 0, ndb = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= dd) continue;
        if (side[v] == 0) defA[nda++] = v;
        else defB[ndb++] = v;
    }
    save_state();
    int moved = 0;
    if (nda + ndb > 0 && rint_(2) == 0) {
        int v;
        if (ndb == 0 || (nda > 0 && rint_(2) == 0)) v = defA[rint_(nda)];
        else v = defB[rint_(ndb)];
        moved = move_transfer(v);
    } else {
        moved = move_switch();
    }
    if (!moved) return;
    greedy_add();
    long long c = cost();
    if (c <= cur_cost || rfloat() < exp(-(double)(c - cur_cost) / T)) {
        cur_cost = c;
    } else {
        restore_state();
    }
}

int main(int argc, char **argv) {
    dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    deadline = now_s() + tl;

    if (dd < 1 || dd >= DMAX || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 2 || n > NMAXIN || m < 1) {
        printf("0 0\n");
        return 0;
    }
    CAP = n + EXTRA;
    W = (CAP + 63) / 64;
    side = calloc((size_t)CAP, sizeof(int));
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DMAX, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    badj = calloc((size_t)CAP * DMAX, sizeof(int));
    sdeg = calloc((size_t)CAP, sizeof(int));
    sadj = calloc((size_t)CAP * DMAX, sizeof(int));
    defA = calloc((size_t)CAP, sizeof(int));
    defB = calloc((size_t)CAP, sizeof(int));
    bufA = calloc((size_t)CAP * W, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * W, sizeof(uint64_t));
    if (!side || !deg || !adj || !bdeg || !badj || !sdeg || !sadj ||
        !defA || !defB || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }
    N = n;

    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
            deg[u] >= dd || deg[v] >= dd || is_adj(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS 2-colouring. */
    int *queue = malloc(sizeof(int) * (size_t)n);
    if (!queue) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[(size_t)x * DMAX + k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    queue[qt++] = y;
                } else if (side[y] == side[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n; v++) {
        if (side[v] == 0) c0++;
        else c1++;
    }
    if (c0 == 0 || c1 == 0) {
        printf("0 0\n");
        return 0;
    }

    greedy_add();
    cur_cost = cost();
    if (cur_cost == 0) record_best();

    int stage_it = 0;
    while (now_s() < deadline) {
        if (cur_cost == 0) {
            record_best();
            if (N + 2 > CAP) break;
            side[N] = 0;
            deg[N] = 0;
            side[N + 1] = 1;
            deg[N + 1] = 0;
            N += 2;
            greedy_add();
            cur_cost = cost();
            stage_it = 0;
            continue;
        }
        double frac = (double)stage_it / (double)GROW_STAGE;
        if (frac > 1.0) frac = 1.0;
        double T = 1.2 * (1.0 - frac) + 0.05;
        step(T);
        stage_it++;
        if (stage_it >= GROW_STAGE && cur_cost != 0) {
            /* Give up on this growth attempt: return to the best valid graph. */
            N = bestN;
            memcpy(deg, bdeg, sizeof(int) * (size_t)N);
            memcpy(adj, badj, sizeof(int) * (size_t)N * DMAX);
            cur_cost = 0;
            stage_it = 0;
        }
    }

    if (bestN < 1) {
        printf("0 0\n");
        return 0;
    }
    long long mm = 0;
    for (int v = 0; v < bestN; v++) mm += bdeg[v];
    mm /= 2;
    printf("%d %lld\n", bestN, mm);
    for (int v = 0; v < bestN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[(size_t)v * DMAX + k];
            if (u > v) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the group-lift search, then growth.
# Every stage only replaces the current best when its output passes is_valid,
# so the function always returns a valid graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(3.0, min(0.85 * time_limit, time_limit - 7.0))
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

    # Stage 1: group-lift breakout search, seeded with the best known order.
    if d >= 3 and D >= 3:
        left = deadline - time.monotonic()
        b1 = 0.70 * left - 0.5
        if b1 >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                                timeout=b1 + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Stage 2: grow the best graph by vertex pairs with annealing repair.
    if d >= 2 and D >= 2:
        left = deadline - time.monotonic() - 0.5
        if left >= 2.0:
            try:
                out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{left:.2f}"],
                                stdin_graph=best, timeout=left + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
