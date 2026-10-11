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
# Stage 2 C engine: vertex augmentation with simulated annealing on general
# bipartite graphs (a different search space from the bi-Cayley stage).
#
# State: an edge list with A-endpoint eu[e] and B-endpoint ev[e], kept in a
# bit adjacency matrix. Augment by 2 vertices (one per side): remove a matching
# of DEG edges, then attach the freed stubs to the two new vertices. Repair by
# degree-preserving double-edge swaps, minimising the number of vertex pairs at
# distance greater than DIAM (counted with bitset BFS). Any state of cost 0 is
# a valid graph and is saved as the new best. The original graph is always kept.
# ----------------------------------------------------------------------------

AUG_C = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int DEG = 3, DIAM = 3;
static int NMAX = 0, W = 0;
static int n = 0, m = 0;
static int *eu = NULL, *ev = NULL;
static int *bu = NULL, *bv = NULL;
static int bn = 0, bm = 0;
static unsigned char *adjm = NULL;
static int *deg = NULL, *adj = NULL;
static uint64_t *bitA = NULL, *bitB = NULL;
static int *picked = NULL;
static unsigned char *usedA = NULL, *usedB = NULL;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static inline void setadj(int a, int b, unsigned char val) {
    adjm[(size_t)a * NMAX + b] = val;
    adjm[(size_t)b * NMAX + a] = val;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long bad_pairs(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int a = eu[e], b = ev[e];
        adj[(size_t)a * DEG + deg[a]++] = b;
        adj[(size_t)b * DEG + deg[b]++] = a;
    }
    uint64_t *cur = bitA, *nxt = bitB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[(size_t)v * DEG + k];
                const uint64_t *src = cur + (size_t)u * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long unreached = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(cur[(size_t)v * W + w]);
        unreached += n - c;
    }
    return unreached / 2;
}

static void rebuild_adjm(void) {
    memset(adjm, 0, (size_t)NMAX * NMAX);
    for (int e = 0; e < m; e++) setadj(eu[e], ev[e], 1);
}

static void save_best(void) {
    bn = n;
    bm = m;
    memcpy(bu, eu, sizeof(int) * (size_t)m);
    memcpy(bv, ev, sizeof(int) * (size_t)m);
}

static void load_best(void) {
    n = bn;
    m = bm;
    memcpy(eu, bu, sizeof(int) * (size_t)m);
    memcpy(ev, bv, sizeof(int) * (size_t)m);
    rebuild_adjm();
}

/* Add two vertices x (side A, id n) and y (side B, id n+1). */
static int add_pair(void) {
    if (m < DEG) return 0;
    int x = n, y = n + 1;
    memset(usedA, 0, (size_t)NMAX);
    memset(usedB, 0, (size_t)NMAX);
    int cnt = 0;
    for (long tries = 0; cnt < DEG && tries < 200000; tries++) {
        int e = rint_(m);
        int a = eu[e], b = ev[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        picked[cnt++] = e;
    }
    if (cnt < DEG) return 0;
    int base = m;
    for (int k = 0; k < DEG; k++) {
        int e = picked[k];
        int a = eu[e], b = ev[e];
        setadj(a, b, 0);
        eu[e] = a;
        ev[e] = y;
        setadj(a, y, 1);
        eu[base + k] = x;
        ev[base + k] = b;
        setadj(x, b, 1);
    }
    m = base + DEG;
    n += 2;
    return 1;
}

/* Double-edge swap: edge e1 becomes (A1,B1), edge e2 becomes (A2,B2). */
static void swap_apply(int e1, int e2, int A1, int B1, int A2, int B2) {
    eu[e1] = A1;
    ev[e1] = B1;
    eu[e2] = A2;
    ev[e2] = B2;
    setadj(A1, B1, 0);
    setadj(A2, B2, 0);
    setadj(A1, B2, 1);
    setadj(A2, B1, 1);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int extra = argc > 5 ? atoi(argv[5]) : 200;
    if (DEG < 1 || DIAM < 1 || extra < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0) {
        printf("0 0\n");
        return 0;
    }
    int *ru = malloc(sizeof(int) * (size_t)m0);
    int *rv = malloc(sizeof(int) * (size_t)m0);
    int *dg = calloc((size_t)n0, sizeof(int));
    if (!ru || !rv || !dg) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2 || ru[i] < 0 || rv[i] < 0 ||
            ru[i] >= n0 || rv[i] >= n0 || ru[i] == rv[i]) {
            printf("0 0\n");
            return 0;
        }
        dg[ru[i]]++;
        dg[rv[i]]++;
    }
    for (int v = 0; v < n0; v++) {
        if (dg[v] > DEG) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Bipartition by BFS colouring. */
    int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *fillp = malloc(sizeof(int) * (size_t)n0);
    int *nb = malloc(sizeof(int) * (size_t)(2 * m0));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *stk = malloc(sizeof(int) * (size_t)n0);
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + dg[v];
    for (int v = 0; v < n0; v++) fillp[v] = off[v];
    for (int i = 0; i < m0; i++) {
        nb[fillp[ru[i]]++] = rv[i];
        nb[fillp[rv[i]]++] = ru[i];
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int v = nb[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    NMAX = n0 + extra;
    W = (NMAX + 63) / 64;
    size_t EC = (size_t)NMAX * (size_t)DEG + (size_t)DEG + 4;
    eu = malloc(sizeof(int) * EC);
    ev = malloc(sizeof(int) * EC);
    bu = malloc(sizeof(int) * EC);
    bv = malloc(sizeof(int) * EC);
    deg = malloc(sizeof(int) * (size_t)NMAX);
    adj = malloc(sizeof(int) * (size_t)NMAX * (size_t)DEG);
    bitA = malloc(sizeof(uint64_t) * (size_t)NMAX * (size_t)W);
    bitB = malloc(sizeof(uint64_t) * (size_t)NMAX * (size_t)W);
    picked = malloc(sizeof(int) * (size_t)DEG);
    usedA = malloc((size_t)NMAX);
    usedB = malloc((size_t)NMAX);
    adjm = malloc((size_t)NMAX * (size_t)NMAX);
    if (!eu || !ev || !bu || !bv || !deg || !adj || !bitA || !bitB || !picked ||
        !usedA || !usedB || !adjm) {
        printf("0 0\n");
        return 0;
    }

    n = n0;
    m = m0;
    for (int i = 0; i < m0; i++) {
        if (col[ru[i]] == 0) {
            eu[i] = ru[i];
            ev[i] = rv[i];
        } else {
            eu[i] = rv[i];
            ev[i] = ru[i];
        }
    }
    rebuild_adjm();
    if (bad_pairs() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    double t0 = now_s();
    double deadline = t0 + tl;
    while (now_s() < deadline && n + 2 <= NMAX) {
        load_best();
        double now = now_s();
        double rem = deadline - now;
        if (rem < 0.2) break;
        double att = rem * 0.35;
        if (att < 2.0) att = rem;
        double att_end = now + att;
        if (att_end > deadline) att_end = deadline;

        if (!add_pair()) break;
        long long cur = bad_pairs();
        const double T_hi = 1.5, T_lo = 0.1;
        double T = T_hi;
        double astart = now;
        long it = 0;
        while (cur > 0) {
            if ((it & 31) == 0) {
                double t = now_s();
                if (t >= att_end) break;
                double f = (t - astart) / (att_end - astart);
                if (f < 0) f = 0;
                if (f > 1) f = 1;
                T = T_hi * pow(T_lo / T_hi, f);
            }
            it++;
            int e1 = rint_(m), e2 = rint_(m);
            if (e1 == e2) continue;
            int a1 = eu[e1], b1 = ev[e1], a2 = eu[e2], b2 = ev[e2];
            if (a1 == a2 || b1 == b2) continue;
            if (adjm[(size_t)a1 * NMAX + b2] || adjm[(size_t)a2 * NMAX + b1]) continue;
            swap_apply(e1, e2, a1, b1, a2, b2);
            long long nc = bad_pairs();
            long long delta = nc - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = nc;
            } else {
                swap_apply(e1, e2, a1, b2, a2, b1);
            }
        }
        if (cur == 0) save_best();
    }

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then bi-Cayley search, then augmentation.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.90 * time_limit, time_limit - 5.0))

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
        # Stage 1: bi-Cayley search for a large regular seed graph.
        total = deadline - time.monotonic() - 1.0
        if total >= 4.0:
            stage1 = 0.45 * total
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{stage1:.2f}", best_n],
                                timeout=stage1 + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: augment the best graph by two vertices at a time and repair
        # by simulated annealing over degree-preserving swaps. The C program
        # only prints graphs with zero bad pairs; the original is kept otherwise.
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 3.0 and lib.is_valid(best[0], best[1], d, D):
            try:
                out = lib.run_c(AUG_C, [d, D, seed + 1, f"{remaining:.2f}"],
                                stdin_graph=best, timeout=remaining + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
