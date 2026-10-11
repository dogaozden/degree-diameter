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


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# C engine.
# Mode 0: bi-Cayley search with breakout local search (clause weighting),
#         coordinate polish, and iterated local search from near-misses.
# Mode 1: augmentation of a d-regular bipartite graph read from stdin.
#         Each attempt removes a random matching of d edges, adds two new
#         vertices x (side A) and y (side B), joins x to the B-ends and y to
#         the A-ends of the removed matching (keeps every degree = d), then
#         repairs distance violations with random degree-preserving 2-switches.
#         Cost 0 means valid. Each success becomes the new base graph.
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

#define MAXADD 60
#define LS_ITERS 200
#define ACCEPT_PCT 3

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

/* ========================================================================
   Augmentation mode (mode 1). The base graph is d-regular, bipartite,
   valid. Edge i joins EA[i] (side 0) to EB[i] (side 1).
   ======================================================================== */

static int ACAP = 0;                 /* vertex capacity */
static int MCAP = 0;                 /* edge capacity */
static int AN = 0, AM = 0;           /* working graph */
static int BSN = 0, BSM = 0;         /* best valid graph so far */
static int *EA = NULL, *EB = NULL;
static int *BEA = NULL, *BEB = NULL;
static int *PERM = NULL, *REM = NULL;
static int TA[MAXD + 1], TB[MAXD + 1];
static unsigned char *MAT = NULL;   /* MAT[a*ACAP+b] = 1 if edge (a side0, b side1) */
static unsigned char *USEA = NULL, *USEB = NULL;
static int *ADJ = NULL, *DEG = NULL, *VIS = NULL, *QQ = NULL, *COL = NULL;
static int VST = 0;

static void aug_alloc(int n0) {
    ACAP = n0 + 2 * MAXADD + 4;
    MCAP = ACAP * Dd + 8;
    EA = malloc(sizeof(int) * (size_t)MCAP);
    EB = malloc(sizeof(int) * (size_t)MCAP);
    BEA = malloc(sizeof(int) * (size_t)MCAP);
    BEB = malloc(sizeof(int) * (size_t)MCAP);
    PERM = malloc(sizeof(int) * (size_t)MCAP);
    REM = malloc(sizeof(int) * (size_t)MCAP);
    MAT = calloc((size_t)ACAP * (size_t)ACAP, 1);
    USEA = calloc((size_t)ACAP, 1);
    USEB = calloc((size_t)ACAP, 1);
    ADJ = malloc(sizeof(int) * (size_t)ACAP * (size_t)Dd);
    DEG = malloc(sizeof(int) * (size_t)ACAP);
    VIS = calloc((size_t)ACAP, sizeof(int));
    QQ = malloc(sizeof(int) * (size_t)ACAP);
    COL = malloc(sizeof(int) * (size_t)ACAP);
    if (!EA || !EB || !BEA || !BEB || !PERM || !REM || !MAT || !USEA || !USEB ||
        !ADJ || !DEG || !VIS || !QQ || !COL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static void mat_rebuild(void) {
    memset(MAT, 0, (size_t)ACAP * (size_t)ACAP);
    for (int i = 0; i < AM; i++) MAT[(size_t)EA[i] * ACAP + EB[i]] = 1;
}

static void aug_build_adj(void) {
    for (int v = 0; v < AN; v++) DEG[v] = 0;
    for (int i = 0; i < AM; i++) {
        int a = EA[i], b = EB[i];
        ADJ[a * Dd + DEG[a]++] = b;
        ADJ[b * Dd + DEG[b]++] = a;
    }
}

/* Number of unordered vertex pairs at distance > DD in the working graph. */
static long long aug_cost(void) {
    aug_build_adj();
    int N = AN;
    long long unreached = 0;
    for (int s = 0; s < N; s++) {
        VST++;
        int head = 0, tail = 0;
        QQ[tail++] = s;
        VIS[s] = VST;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QQ[head++];
                for (int t = 0; t < Dd; t++) {
                    int v = ADJ[u * Dd + t];
                    if (VIS[v] != VST) {
                        VIS[v] = VST;
                        QQ[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached / 2;
}

/* Starting from the best graph, delete a random matching of Dd edges and
   attach a new A-vertex x = BSN and B-vertex y = BSN+1 to it. */
static int aug_insert(void) {
    int N0 = BSN, M0 = BSM;
    if (N0 + 2 > ACAP) return 0;
    memcpy(EA, BEA, sizeof(int) * (size_t)M0);
    memcpy(EB, BEB, sizeof(int) * (size_t)M0);
    for (int i = 0; i < M0; i++) {
        PERM[i] = i;
        REM[i] = 0;
    }
    for (int i = M0 - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = PERM[i];
        PERM[i] = PERM[j];
        PERM[j] = t;
    }
    memset(USEA, 0, (size_t)N0);
    memset(USEB, 0, (size_t)N0);
    int nc = 0;
    for (int k = 0; k < M0 && nc < Dd; k++) {
        int idx = PERM[k];
        int a = EA[idx], b = EB[idx];
        if (!USEA[a] && !USEB[b]) {
            USEA[a] = 1;
            USEB[b] = 1;
            REM[idx] = 1;
            TA[nc] = a;
            TB[nc] = b;
            nc++;
        }
    }
    if (nc < Dd) return 0;
    int w = 0;
    for (int i = 0; i < M0; i++) {
        if (!REM[i]) {
            EA[w] = EA[i];
            EB[w] = EB[i];
            w++;
        }
    }
    int x = N0, y = N0 + 1;
    for (int t = 0; t < Dd; t++) {
        EA[w] = x;
        EB[w] = TB[t];
        w++;
        EA[w] = TA[t];
        EB[w] = y;
        w++;
    }
    AM = w;
    AN = N0 + 2;
    mat_rebuild();
    return 1;
}

/* Random degree-preserving 2-switches on edges (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
   Accept if the cost does not increase, or with a small probability. */
static long long aug_search(long long cur, int iters) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 7) == 0 && now_s() > deadline) break;
        int i = rint_(AM), j = rint_(AM);
        if (i == j) continue;
        int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
        if (a1 == a2 || b1 == b2) continue;
        if (MAT[(size_t)a1 * ACAP + b2] || MAT[(size_t)a2 * ACAP + b1]) continue;
        MAT[(size_t)a1 * ACAP + b1] = 0;
        MAT[(size_t)a2 * ACAP + b2] = 0;
        MAT[(size_t)a1 * ACAP + b2] = 1;
        MAT[(size_t)a2 * ACAP + b1] = 1;
        EB[i] = b2;
        EB[j] = b1;
        long long c2 = aug_cost();
        if (c2 <= cur || rint_(100) < ACCEPT_PCT) {
            cur = c2;
        } else {
            EB[i] = b1;
            EB[j] = b2;
            MAT[(size_t)a1 * ACAP + b2] = 0;
            MAT[(size_t)a2 * ACAP + b1] = 0;
            MAT[(size_t)a1 * ACAP + b1] = 1;
            MAT[(size_t)a2 * ACAP + b2] = 1;
        }
    }
    return cur;
}

static void aug_save(void) {
    memcpy(BEA, EA, sizeof(int) * (size_t)AM);
    memcpy(BEB, EB, sizeof(int) * (size_t)AM);
    BSN = AN;
    BSM = AM;
}

/* Reads "n m" and m edges from stdin. Accepts only a simple d-regular
   bipartite graph; otherwise returns 0. */
static int aug_read(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || m <= 0 || n > 200000) return 0;
    int *U = malloc(sizeof(int) * (size_t)m);
    int *V = malloc(sizeof(int) * (size_t)m);
    if (!U || !V) return 0;
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &U[i], &V[i]) != 2) return 0;
        if (U[i] < 0 || U[i] >= n || V[i] < 0 || V[i] >= n || U[i] == V[i]) return 0;
    }
    aug_alloc(n);
    for (int v = 0; v < n; v++) DEG[v] = 0;
    for (int i = 0; i < m; i++) {
        DEG[U[i]]++;
        DEG[V[i]]++;
    }
    for (int v = 0; v < n; v++)
        if (DEG[v] != Dd) return 0;
    for (int v = 0; v < n; v++) DEG[v] = 0;
    for (int i = 0; i < m; i++) {
        ADJ[U[i] * Dd + DEG[U[i]]++] = V[i];
        ADJ[V[i] * Dd + DEG[V[i]]++] = U[i];
    }
    for (int v = 0; v < n; v++) COL[v] = -1;
    for (int s = 0; s < n; s++) {
        if (COL[s] != -1) continue;
        COL[s] = 0;
        int head = 0, tail = 0;
        QQ[tail++] = s;
        while (head < tail) {
            int u = QQ[head++];
            for (int t = 0; t < Dd; t++) {
                int w = ADJ[u * Dd + t];
                if (COL[w] == -1) {
                    COL[w] = 1 - COL[u];
                    QQ[tail++] = w;
                } else if (COL[w] == COL[u]) {
                    return 0;
                }
            }
        }
    }
    memset(MAT, 0, (size_t)ACAP * (size_t)ACAP);
    AN = n;
    AM = m;
    for (int i = 0; i < m; i++) {
        int a = (COL[U[i]] == 0) ? U[i] : V[i];
        int b = (COL[U[i]] == 0) ? V[i] : U[i];
        EA[i] = a;
        EB[i] = b;
        if (MAT[(size_t)a * ACAP + b]) return 0;
        MAT[(size_t)a * ACAP + b] = 1;
    }
    aug_save();
    free(U);
    free(V);
    return 1;
}

static void aug_run(void) {
    int added = 0;
    while (added < MAXADD && now_s() < deadline) {
        if (!aug_insert()) continue;
        long long c = aug_cost();
        c = aug_search(c, LS_ITERS);
        if (c == 0) {
            aug_save();
            added++;
        }
    }
}

static void aug_print(void) {
    printf("%d %d\n", BSN, BSM);
    for (int i = 0; i < BSM; i++) printf("%d %d\n", BEA[i], BEB[i]);
}

/* ========================================================================
   Main
   ======================================================================== */

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

    double t0 = now_s();
    deadline = t0 + tl;

    if (mode == 1) {
        if (aug_read()) aug_run();
        else {
            printf("0 0\n");
            return 0;
        }
        aug_print();
        return 0;
    }

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
# Python glue: exact constructions, then group search, then augmentation.
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
        # Stage 1: group (bi-Cayley) search seeded with the best known order.
        remaining = deadline - time.monotonic()
        g_budget = (remaining - 1.5) * 0.55
        if g_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{g_budget:.2f}", best_n, 0],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: augmentation of the best regular graph by vertex pairs.
        if _is_regular(best[0], best[1], d):
            a_budget = deadline - time.monotonic() - 1.5
            if a_budget >= 2.0:
                try:
                    out = lib.run_c(C_SOURCE, [d, D, seed + 1, f"{a_budget:.2f}", 0, 1],
                                    stdin_graph=best, timeout=time_limit - 3.0)
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
