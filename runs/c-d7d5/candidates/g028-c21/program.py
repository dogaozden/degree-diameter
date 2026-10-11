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
# C engine 1: bi-Cayley search with breakout local search (clause weighting),
# a unit-weight coordinate polish for near-solutions, and iterated local
# search. Unchanged from the parent.
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
# C engine 2 (NEW): vertex-pair insertion + edge-switch annealing.
#
# Idea: a valid d-regular bipartite graph G with diameter D is extended by two
# new vertices x (side A) and y (side B). Pick d-1 disjoint edges a_t b_t of G,
# delete them, join x to every b_t and y to every a_t, and join x to y. Every
# old vertex keeps its degree, x and y get degree d, and order grows by 2. The
# new graph usually has a few bad pairs (unreached within D). Repair is a
# degree- and bipartition-preserving 2-switch annealing: replace edges
# (a1,b1),(a2,b2) by (a1,b2),(a2,b1), with cost = number of unordered pairs
# farther than D. Costs are computed with bitset ball expansion, about 1 ms
# per evaluation at order ~1100. When cost reaches 0 the graph is saved and the
# insertion repeats from it. Failed attempts restore the last valid graph.
# ----------------------------------------------------------------------------

AUG_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef unsigned long long u64;

#define MAXAUG 60
#define STAG 3000
#define MAXFAIL 40

static u64 rs = 0x2545F4914F6CDD1DULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (u64)n); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int DEG = 3, DIA = 3;
static int N0 = 0, E0 = 0, NMAX = 0, WMAX = 0, ecap = 0;
static int NV = 0, NE = 0;
static int *ea = NULL, *eb = NULL;          /* ea is side A, eb is side B */
static unsigned char *am = NULL;            /* symmetric adjacency, NMAX x NMAX */
static int *coff = NULL, *cnb = NULL, *cdeg = NULL;
static u64 *rowc = NULL, *rown = NULL;
static int bestNV = 0, bestNE = 0;
static int *bea = NULL, *beb = NULL;
static double T_START = 0.0, T_END = 0.0;

#define AM(u, v) am[(size_t)(u) * (size_t)NMAX + (size_t)(v)]

static void am_set(int u, int v, unsigned char x) {
    AM(u, v) = x;
    AM(v, u) = x;
}

static int popc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_csr(void) {
    int N = NV;
    for (int v = 0; v < N; v++) cdeg[v] = 0;
    for (int e = 0; e < NE; e++) {
        cdeg[ea[e]]++;
        cdeg[eb[e]]++;
    }
    coff[0] = 0;
    for (int v = 0; v < N; v++) coff[v + 1] = coff[v] + cdeg[v];
    for (int v = 0; v < N; v++) cdeg[v] = 0;
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        cnb[coff[a] + cdeg[a]++] = b;
        cnb[coff[b] + cdeg[b]++] = a;
    }
}

/* Number of unordered pairs at distance > DIA (including disconnected). */
static long long evalbad(void) {
    int N = NV, Wc = (N + 63) / 64;
    build_csr();
    for (int v = 0; v < N; v++) {
        u64 *r = rowc + (size_t)v * (size_t)WMAX;
        for (int w = 0; w < Wc; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int rd = 0; rd < DIA; rd++) {
        for (int v = 0; v < N; v++) {
            u64 *o = rown + (size_t)v * (size_t)WMAX;
            u64 *s = rowc + (size_t)v * (size_t)WMAX;
            for (int w = 0; w < Wc; w++) o[w] = s[w];
            for (int k = coff[v]; k < coff[v + 1]; k++) {
                u64 *t = rowc + (size_t)cnb[k] * (size_t)WMAX;
                for (int w = 0; w < Wc; w++) o[w] |= t[w];
            }
        }
        u64 *tmp = rowc;
        rowc = rown;
        rown = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = rowc + (size_t)v * (size_t)WMAX;
        int c = 0;
        for (int w = 0; w < Wc; w++) c += popc64(r[w]);
        miss += (long long)(N - c);
    }
    return miss / 2;
}

static void snapshot(void) {
    bestNV = NV;
    bestNE = NE;
    memcpy(bea, ea, sizeof(int) * (size_t)NE);
    memcpy(beb, eb, sizeof(int) * (size_t)NE);
}

static void restore(void) {
    for (int e = 0; e < NE; e++) am_set(ea[e], eb[e], 0);
    NV = bestNV;
    NE = bestNE;
    for (int e = 0; e < NE; e++) {
        ea[e] = bea[e];
        eb[e] = beb[e];
        am_set(ea[e], eb[e], 1);
    }
}

/* Vertex-pair insertion (see the header comment). Returns 0 if no change was made. */
static int augment(void) {
    int k = DEG - 1;
    if (k < 1) return 0;
    if (NV + 2 > NMAX) return 0;
    if (NE + DEG > ecap) return 0;
    if (NE < k) return 0;
    int *perm = malloc(sizeof(int) * (size_t)NE);
    char *usedv = calloc((size_t)NV, 1);
    int *ch = malloc(sizeof(int) * (size_t)k);
    int *ra = malloc(sizeof(int) * (size_t)k);
    int *rb = malloc(sizeof(int) * (size_t)k);
    char *mark = calloc((size_t)NE, 1);
    if (!perm || !usedv || !ch || !ra || !rb || !mark) {
        free(perm);
        free(usedv);
        free(ch);
        free(ra);
        free(rb);
        free(mark);
        return 0;
    }
    for (int e = 0; e < NE; e++) perm[e] = e;
    for (int e = NE - 1; e > 0; e--) {
        int j = rint_(e + 1);
        int t = perm[e];
        perm[e] = perm[j];
        perm[j] = t;
    }
    int cnt = 0;
    for (int t = 0; t < NE && cnt < k; t++) {
        int e = perm[t];
        if (usedv[ea[e]] || usedv[eb[e]]) continue;
        usedv[ea[e]] = 1;
        usedv[eb[e]] = 1;
        ch[cnt] = e;
        ra[cnt] = ea[e];
        rb[cnt] = eb[e];
        cnt++;
    }
    int ok = (cnt == k);
    if (ok) {
        for (int t = 0; t < k; t++) mark[ch[t]] = 1;
        int ne = 0;
        for (int e = 0; e < NE; e++) {
            if (mark[e]) {
                am_set(ea[e], eb[e], 0);
            } else {
                ea[ne] = ea[e];
                eb[ne] = eb[e];
                ne++;
            }
        }
        int x = NV, y = NV + 1;
        NV += 2;
        for (int t = 0; t < k; t++) {
            ea[ne] = x;
            eb[ne] = rb[t];
            am_set(x, rb[t], 1);
            ne++;
            ea[ne] = ra[t];
            eb[ne] = y;
            am_set(ra[t], y, 1);
            ne++;
        }
        ea[ne] = x;
        eb[ne] = y;
        am_set(x, y, 1);
        ne++;
        NE = ne;
    }
    free(perm);
    free(usedv);
    free(ch);
    free(ra);
    free(rb);
    free(mark);
    return ok;
}

int main(int argc, char **argv) {
    DEG = argc > 1 ? atoi(argv[1]) : 3;
    DIA = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;

    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m <= 0 || DEG < 2 || DIA < 1) {
        printf("0 0\n");
        return 0;
    }
    N0 = n;
    E0 = m;
    NMAX = N0 + 2 * MAXAUG + 2;
    WMAX = (NMAX + 63) / 64;
    ecap = E0 + (MAXAUG + 2) * DEG + 16;

    ea = malloc(sizeof(int) * (size_t)ecap);
    eb = malloc(sizeof(int) * (size_t)ecap);
    bea = malloc(sizeof(int) * (size_t)ecap);
    beb = malloc(sizeof(int) * (size_t)ecap);
    cnb = malloc(sizeof(int) * (size_t)2 * (size_t)ecap);
    am = calloc((size_t)NMAX * (size_t)NMAX, 1);
    coff = malloc(sizeof(int) * (size_t)(NMAX + 1));
    cdeg = malloc(sizeof(int) * (size_t)NMAX);
    rowc = calloc((size_t)NMAX * (size_t)WMAX, sizeof(u64));
    rown = calloc((size_t)NMAX * (size_t)WMAX, sizeof(u64));
    if (!ea || !eb || !bea || !beb || !cnb || !am || !coff || !cdeg || !rowc || !rown) {
        printf("0 0\n");
        return 0;
    }

    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v) {
            printf("0 0\n");
            return 0;
        }
        ea[e] = u;
        eb[e] = v;
    }

    /* 2-colour the input; reject if not bipartite, then orient edges A->B. */
    NV = N0;
    NE = E0;
    build_csr();
    int *col = malloc(sizeof(int) * (size_t)N0);
    int *q = malloc(sizeof(int) * (size_t)N0);
    for (int v = 0; v < N0; v++) col[v] = -1;
    int bip = 1;
    for (int s = 0; s < N0 && bip; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t && bip) {
            int u = q[h++];
            for (int k = coff[u]; k < coff[u + 1]; k++) {
                int v = cnb[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    bip = 0;
                    break;
                }
            }
        }
    }
    if (!bip) {
        printf("0 0\n");
        return 0;
    }
    for (int e = 0; e < NE; e++) {
        if (col[ea[e]] == 1) {
            int t = ea[e];
            ea[e] = eb[e];
            eb[e] = t;
        }
        am_set(ea[e], eb[e], 1);
    }
    free(col);
    free(q);

    double t0 = now_s();
    T_START = t0;
    T_END = t0 + tl;

    if (evalbad() != 0) {
        printf("0 0\n");
        return 0;
    }
    snapshot();

    int fails = 0;
    while (now_s() < T_END && fails < MAXFAIL) {
        if (!augment()) {
            fails++;
            continue;
        }
        long long cur = evalbad();
        long long lbest = cur;
        int stag = 0;
        while (cur > 0 && stag < STAG) {
            double now = now_s();
            if (now >= T_END) break;
            double frac = (now - T_START) / (T_END - T_START);
            double T = 1.2 * (1.0 - frac) + 0.05;
            int i = rint_(NE), j = rint_(NE);
            if (i == j) {
                stag++;
                continue;
            }
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2 || AM(a1, b2) || AM(a2, b1)) {
                stag++;
                continue;
            }
            am_set(a1, b1, 0);
            am_set(a2, b2, 0);
            am_set(a1, b2, 1);
            am_set(a2, b1, 1);
            eb[i] = b2;
            eb[j] = b1;
            long long nb = evalbad();
            long long dl = nb - cur;
            if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                cur = nb;
                if (nb < lbest) {
                    lbest = nb;
                    stag = 0;
                } else {
                    stag++;
                }
            } else {
                am_set(a1, b2, 0);
                am_set(a2, b1, 0);
                am_set(a1, b1, 1);
                am_set(a2, b2, 1);
                eb[i] = b1;
                eb[j] = b2;
                stag++;
            }
        }
        if (cur == 0) {
            snapshot();
            fails = 0;
        } else {
            restore();
            fails++;
        }
    }

    printf("%d %d\n", bestNV, bestNE);
    for (int e = 0; e < bestNE; e++) printf("%d %d\n", bea[e], beb[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _augment(d, D, n, edges, seed, budget):
    """Run the vertex-pair insertion annealer on a valid graph; return (n, edges) or None."""
    if budget < 2.0:
        return None
    try:
        out = lib.run_c(AUG_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(n, edges), timeout=budget + 5.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


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

    # Stage 1: bi-Cayley breakout search in C, seeded with the best known order.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        group_budget = 0.5 * remaining - 1.0
        if group_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{group_budget:.2f}", best_n],
                                timeout=group_budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    # Stage 2: grow the best valid graph by vertex-pair insertion + edge-switch annealing.
    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 2.0:
            got = _augment(d, D, best[0], best[1], seed + 1, remaining)
            if got is not None:
                consider(got[0], got[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
