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
# C engine 1 (parent): bi-Cayley search with breakout local search (clause
# weighting), a unit-weight coordinate polish for near-solutions, and iterated
# local search on the best near-miss.
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
            K = (rint_(100) < 75) ? 1 : 2;
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
# C engine 2 (new): unstructured annealing that GROWS a valid graph.
# State: bipartite multigraph-free graph, A-vertices are edge endpoints ea[],
# B-vertices eb[]. Moves are degree-preserving double edge swaps. Cost is the
# number of ordered vertex pairs farther than D apart (bitset BFS). When cost
# hits 0 the graph is saved and grown by one A-vertex and one B-vertex, which
# are wired in by splitting random edges. Stale growth attempts restart from
# the last saved valid graph. The best valid graph is printed at the end.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 4096
#define MAXDEG 32
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 256)
#define STALE_LIMIT 6000
#define REHEAT_EVERY 3000
#define T_HOT 2.0
#define T_COLD 0.3

static int dg = 3, diam = 3;
static int N = 0, M = 0;
static int deg[MAXN];
static int nbr[MAXN][MAXDEG];
static int ea[MAXE], eb[MAXE];
static int bestN = 0, bestM = 0;
static int bea[MAXE], beb[MAXE];
static int col[MAXN], qu[MAXN];
static uint64_t bufA[(size_t)MAXN * MAXW], bufB[(size_t)MAXN * MAXW];
static uint64_t rs = 0x2545F4914F6CDD1DULL;
static double deadline = 0.0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }

static double unif(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
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

static int is_adj(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nbr[a][k] == b) return 1;
    return 0;
}

static void remove_nb(int v, int u) {
    for (int k = 0; k < deg[v]; k++) {
        if (nbr[v][k] == u) {
            nbr[v][k] = nbr[v][--deg[v]];
            return;
        }
    }
}

static void add_nb(int v, int u) {
    if (deg[v] >= MAXDEG) {
        fprintf(stderr, "degree overflow\n");
        exit(1);
    }
    nbr[v][deg[v]++] = u;
}

static void add_edge(int a, int b) {
    if (M >= MAXE) {
        fprintf(stderr, "edge overflow\n");
        exit(1);
    }
    ea[M] = a;
    eb[M] = b;
    M++;
    add_nb(a, b);
    add_nb(b, a);
}

/* Replace edges e1=(a1,b1), e2=(a2,b2) by (na1,nb1), (na2,nb2).
   Degrees are preserved when the new endpoints are a permutation of the old. */
static void apply_pair(int e1, int e2, int na1, int nb1, int na2, int nb2) {
    remove_nb(ea[e1], eb[e1]);
    remove_nb(eb[e1], ea[e1]);
    remove_nb(ea[e2], eb[e2]);
    remove_nb(eb[e2], ea[e2]);
    ea[e1] = na1;
    eb[e1] = nb1;
    ea[e2] = na2;
    eb[e2] = nb2;
    add_nb(na1, nb1);
    add_nb(nb1, na1);
    add_nb(na2, nb2);
    add_nb(nb2, na2);
}

/* Ordered pairs (v,w) with dist(v,w) > diam. Zero means valid. */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *A = bufA, *B = bufB;
    memset(A, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        A[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int lv = 0; lv < diam; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = B + (size_t)v * W;
            memcpy(dst, A + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = A + (size_t)nbr[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = A;
        A = B;
        B = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(A[(size_t)v * W + (size_t)w]);
        bad += N - c;
    }
    return bad;
}

static int bipartite_color(void) {
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int k = 0; k < deg[u]; k++) {
                int w = nbr[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    qu[tail++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(bea, ea, sizeof(int) * (size_t)M);
    memcpy(beb, eb, sizeof(int) * (size_t)M);
}

static void load_best(void) {
    N = bestN;
    M = bestM;
    memset(deg, 0, sizeof(deg));
    for (int e = 0; e < M; e++) {
        ea[e] = bea[e];
        eb[e] = beb[e];
        add_nb(ea[e], eb[e]);
        add_nb(eb[e], ea[e]);
    }
}

/* Add new A-vertex a=N and B-vertex b=N+1, joined to each other, then fill
   both to degree dg by splitting random old edges (x,y) into (x,b),(a,y). */
static void grow(void) {
    int a = N, b = N + 1;
    N += 2;
    deg[a] = 0;
    deg[b] = 0;
    add_edge(a, b);
    int guard = 0;
    while (deg[a] < dg && guard < 200000) {
        guard++;
        int e = rnd_int(M);
        int x = ea[e], y = eb[e];
        if (x == a || y == b) continue;
        if (is_adj(x, b) || is_adj(a, y)) continue;
        remove_nb(x, y);
        remove_nb(y, x);
        ea[e] = x;
        eb[e] = b;
        add_nb(x, b);
        add_nb(b, x);
        add_edge(a, y);
    }
}

static void random_start(int n0, int d) {
    int h = n0 / 2;
    if (h < 2) h = 2;
    memset(deg, 0, sizeof(deg));
    N = 2 * h;
    M = 0;
    int *perm = malloc(sizeof(int) * (size_t)h);
    if (!perm) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    for (int k = 0; k < d; k++) {
        for (int i = 0; i < h; i++) perm[i] = i;
        for (int i = h - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int a = 0; a < h; a++) {
            int b = perm[a];
            if (deg[a] < d && deg[h + b] < d && !is_adj(a, h + b))
                add_edge(a, h + b);
        }
    }
    free(perm);
}

static void output_best(void) {
    if (bestN <= 0) {
        printf("0 0\n");
        return;
    }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++)
        printf("%d %d\n", bea[e], beb[e]);
}

int main(int argc, char **argv) {
    dg = argc > 1 ? atoi(argv[1]) : 3;
    diam = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (dg < 1 || dg > MAXDEG || diam < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();
    deadline = now_s() + tl;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    int ok = 1;
    if (n < 0 || m < 0 || n > MAXN - 8 || m > MAXE - 8 * dg - 16) ok = 0;

    if (ok && n > 0) {
        int *tu = malloc(sizeof(int) * (size_t)(m + 1));
        int *tv = malloc(sizeof(int) * (size_t)(m + 1));
        if (!tu || !tv) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < m && ok; i++)
            if (scanf("%d %d", &tu[i], &tv[i]) != 2) ok = 0;
        memset(deg, 0, sizeof(deg));
        N = n;
        M = 0;
        for (int i = 0; i < m && ok; i++) {
            int u = tu[i], v = tv[i];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) ok = 0;
            else if (deg[u] >= dg || deg[v] >= dg || is_adj(u, v)) ok = 0;
            else {
                add_nb(u, v);
                add_nb(v, u);
            }
        }
        if (ok && !bipartite_color()) ok = 0;
        if (ok) {
            M = 0;
            for (int i = 0; i < m; i++) {
                int u = tu[i], v = tv[i];
                if (col[u] == 0) {
                    ea[M] = u;
                    eb[M] = v;
                } else {
                    ea[M] = v;
                    eb[M] = u;
                }
                M++;
            }
        }
        free(tu);
        free(tv);
    } else if (ok) {
        random_start(min_n > 0 ? min_n : 4 * dg, dg);
    }

    if (!ok || N < 2 || M < 2) {
        printf("0 0\n");
        return 0;
    }

    long long cur = eval_cost();
    if (cur == 0) save_best();
    long long minc = cur;
    double T = T_HOT;
    int stale = 0;

    while (now_s() < deadline) {
        if (cur == 0) {
            save_best();
            if (N + 2 > MAXN - 8 || M + dg + 8 >= MAXE) break;
            grow();
            cur = eval_cost();
            minc = cur;
            stale = 0;
            T = T_HOT;
            continue;
        }
        if (bestN > 0 && stale > STALE_LIMIT) {
            load_best();
            if (N + 2 > MAXN - 8 || M + dg + 8 >= MAXE) break;
            grow();
            cur = eval_cost();
            minc = cur;
            stale = 0;
            T = T_HOT;
            continue;
        }
        if (M < 2) break;
        int e1 = rnd_int(M), e2 = rnd_int(M);
        if (e1 == e2) {
            stale++;
            continue;
        }
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2 || is_adj(a1, b2) || is_adj(a2, b1)) {
            stale++;
            continue;
        }
        apply_pair(e1, e2, a1, b2, a2, b1);
        long long nc = eval_cost();
        long long dl = nc - cur;
        if (dl <= 0 || unif() < exp(-(double)dl / T)) {
            cur = nc;
            if (cur < minc) {
                minc = cur;
                stale = 0;
            } else {
                stale++;
            }
        } else {
            apply_pair(e1, e2, a1, b1, a2, b2);
            stale++;
        }
        T *= 0.9995;
        if (T < T_COLD) T = T_COLD;
        if (stale > 0 && stale % REHEAT_EVERY == 0) T = T_HOT;
    }

    if (bestN > 0) {
        load_best();
        if (eval_cost() != 0) bestN = 0;
    }
    output_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _grow_with_sa(graph, d, D, seed, budget):
    """Run the annealing grower on a valid graph; return (n, edges) it found."""
    out = lib.run_c(SA_SOURCE, [d, D, seed, f"{budget:.2f}", 0],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(3.0, min(0.85 * time_limit, time_limit - 6.0))

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
        remaining = deadline - time.monotonic()

        # Stage 1: parent's group-based breakout search for a large valid graph.
        frac = 0.55 if D >= 5 else 0.85
        c_budget = remaining * frac - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best_n],
                                timeout=c_budget + 4.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

        # Stage 2: grow the best valid graph found so far by unstructured
        # annealing with degree-preserving edge swaps and vertex-pair insertion.
        remaining = deadline - time.monotonic() - 2.0
        if remaining >= 2.0:
            try:
                n, e = _grow_with_sa(best, d, D, seed + 1, remaining)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
