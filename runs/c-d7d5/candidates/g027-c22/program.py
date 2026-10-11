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
# local search on the best near-miss. Used as the stage-1 seed search.
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
# C engine 2 (new): growth by annealing. Starts from a valid bipartite graph
# with max degree d and diameter <= D, then repeatedly adds one A vertex and
# one B vertex (isolated) and anneals the number of unordered pairs at
# distance > D. Moves keep bipartiteness and max degree <= d:
#   add     : edge between a deficient A vertex and a deficient B vertex
#   insert  : replace edge (a,b) by (a,y),(x,b) for deficient x (A), y (B)
#   switch  : replace (a,b),(c,e) by (a,e),(c,b) (keeps all degrees)
# Whenever the cost reaches 0 the graph is saved and two vertices are added.
# ----------------------------------------------------------------------------

GROW_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2600
#define MAXD 64
#define WMAX ((NMAX + 63) / 64)

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int Dd = 3, DD = 3;
static int n = 0, M = 0;
static int side[NMAX], deg[NMAX], ncnt[NMAX], defs[NMAX], qbuf[NMAX];
static unsigned char adjm[NMAX * NMAX];
static int eu[NMAX * MAXD], ev[NMAX * MAXD];
static int nbr[NMAX * MAXD];
static int bestEu[NMAX * MAXD], bestEv[NMAX * MAXD];
static int bestN = 0, bestM = 0;
static uint64_t bufA[NMAX * WMAX], bufB[NMAX * WMAX];

static void aset(int a, int b, int v) {
    adjm[a * NMAX + b] = (unsigned char)v;
    adjm[b * NMAX + a] = (unsigned char)v;
}

static void build_nbr(void) {
    for (int v = 0; v < n; v++) ncnt[v] = 0;
    for (int e = 0; e < M; e++) {
        int a = eu[e], b = ev[e];
        nbr[a * Dd + ncnt[a]++] = b;
        nbr[b * Dd + ncnt[b]++] = a;
    }
}

/* Number of unordered pairs at distance > DD (unreachable counts). */
static long long eval_cost(void) {
    build_nbr();
    int W = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int step = 0; step < DD; step++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int t = 0; t < ncnt[v]; t++) {
                const uint64_t *src = cur + (size_t)nbr[v * Dd + t] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(cur[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_best(void) {
    bestN = n;
    bestM = M;
    memcpy(bestEu, eu, sizeof(int) * (size_t)M);
    memcpy(bestEv, ev, sizeof(int) * (size_t)M);
}

static int pick_def(int s) {
    int c = 0;
    for (int v = 0; v < n; v++)
        if (side[v] == s && deg[v] < Dd) defs[c++] = v;
    if (c == 0) return -1;
    return defs[rint_(c)];
}

/* Undo log: type 0 = replace edge i (old endpoints oa, ob); type 1 = appended edge i. */
typedef struct {
    int type;
    int i;
    int oa, ob;
} Op;

static Op logv[8];
static int nlog = 0;

static void op_replace(int i, int a, int b) {
    int oa = eu[i], ob = ev[i];
    aset(oa, ob, 0);
    deg[oa]--;
    deg[ob]--;
    eu[i] = a;
    ev[i] = b;
    aset(a, b, 1);
    deg[a]++;
    deg[b]++;
    logv[nlog].type = 0;
    logv[nlog].i = i;
    logv[nlog].oa = oa;
    logv[nlog].ob = ob;
    nlog++;
}

static void op_append(int a, int b) {
    int i = M++;
    eu[i] = a;
    ev[i] = b;
    aset(a, b, 1);
    deg[a]++;
    deg[b]++;
    logv[nlog].type = 1;
    logv[nlog].i = i;
    logv[nlog].oa = 0;
    logv[nlog].ob = 0;
    nlog++;
}

static void undo_all(void) {
    while (nlog > 0) {
        Op o = logv[--nlog];
        int a = eu[o.i], b = ev[o.i];
        if (o.type == 0) {
            aset(a, b, 0);
            deg[a]--;
            deg[b]--;
            eu[o.i] = o.oa;
            ev[o.i] = o.ob;
            aset(o.oa, o.ob, 1);
            deg[o.oa]++;
            deg[o.ob]++;
        } else {
            aset(a, b, 0);
            deg[a]--;
            deg[b]--;
            M--;
        }
    }
}

static int make_move(void) {
    double r = urand();
    if (r < 0.20) {
        int u = pick_def(0), v = pick_def(1);
        if (u < 0 || v < 0 || adjm[u * NMAX + v]) return 0;
        op_append(u, v);
        return 1;
    } else if (r < 0.35) {
        if (M == 0) return 0;
        int x = pick_def(0), y = pick_def(1);
        if (x < 0 || y < 0) return 0;
        int i = rint_(M);
        int a = eu[i], b = ev[i];
        if (adjm[a * NMAX + y] || adjm[x * NMAX + b]) return 0;
        op_replace(i, a, y);
        op_append(x, b);
        return 1;
    } else {
        if (M < 2) return 0;
        int i = rint_(M), j = rint_(M);
        if (i == j) return 0;
        int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
        if (a == c || b == e) return 0;
        if (adjm[a * NMAX + e] || adjm[c * NMAX + b]) return 0;
        op_replace(i, a, e);
        op_replace(j, c, b);
        return 1;
    }
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    double deadline = now_s() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || n0 > NMAX - 2 ||
        m0 < 0 || m0 > NMAX * MAXD / 2) {
        printf("0 0\n");
        return 0;
    }
    int ok = 1;
    for (int e = 0; e < m0 && ok; e++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) ok = 0;
        else if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) ok = 0;
        else {
            eu[e] = a;
            ev[e] = b;
        }
    }
    n = n0;
    M = m0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < M && ok; e++) {
        int a = eu[e], b = ev[e];
        if (adjm[a * NMAX + b]) ok = 0;
        else {
            aset(a, b, 1);
            deg[a]++;
            deg[b]++;
        }
    }
    for (int v = 0; v < n && ok; v++)
        if (deg[v] > Dd) ok = 0;

    if (ok) {
        build_nbr();
        for (int v = 0; v < n; v++) side[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            qbuf[qt++] = s;
            while (qh < qt && ok) {
                int u = qbuf[qh++];
                for (int t = 0; t < ncnt[u]; t++) {
                    int w = nbr[u * Dd + t];
                    if (side[w] < 0) {
                        side[w] = 1 - side[u];
                        qbuf[qt++] = w;
                    } else if (side[w] == side[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < M; e++) {
        if (side[eu[e]] == 1) {
            int t = eu[e];
            eu[e] = ev[e];
            ev[e] = t;
        }
    }
    long long cur = eval_cost();
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    const double T0 = 3.0, TEND = 0.12;
    const long CYC = 8000;
    long it = 0;
    while (now_s() < deadline) {
        if (cur == 0) {
            save_best();
            if (n + 2 > NMAX - 1) break;
            side[n] = 0;
            side[n + 1] = 1;
            deg[n] = 0;
            deg[n + 1] = 0;
            n += 2;
            cur = eval_cost();
            it = 0;
            continue;
        }
        double ph = (double)(it % CYC) / (double)CYC;
        double T = T0 * pow(TEND / T0, ph);
        nlog = 0;
        if (!make_move()) {
            it++;
            continue;
        }
        long long nc = eval_cost();
        long long dl = nc - cur;
        if (dl <= 0 || urand() < exp(-(double)dl / T)) {
            cur = nc;
            if (cur == 0) save_best();
        } else {
            undo_all();
        }
        it++;
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then for D >= 5 a two-stage C run:
# seed search (parent engine), then annealing growth of the best graph.
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
        total = deadline - time.monotonic() - 1.5
        if D >= 5 and total >= 8.0:
            # Stage 1: lift search for a large seed graph.
            t1 = 0.5 * total
            to1 = max(1.0, min(t1 + 3.0, time_limit - (time.monotonic() - start) - 1.0))
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{t1:.2f}", best_n], timeout=to1)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass
            # Stage 2: annealing growth from the best valid graph so far.
            t2 = deadline - time.monotonic() - 1.0
            if t2 >= 2.0:
                to2 = max(1.0, min(t2 + 3.0, time_limit - (time.monotonic() - start) - 1.0))
                try:
                    out = lib.run_c(GROW_SOURCE, [d, D, seed, f"{t2:.2f}"],
                                    stdin_graph=best, timeout=to2)
                    consider(*lib.parse_graph_text(out))
                except Exception:
                    pass
        elif total >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{total:.2f}", best_n],
                                timeout=time_limit - 3.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
