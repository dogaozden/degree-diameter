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
            /* Mostly K = 1 (bi-Cayley), sometimes K = 2. */
            K = (rint_(100) < 75) ? 1 : 2;
            long long g0 = (long long)best_n / (2 * K) + 1;
            long long span = g0 / 25 + 6;
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
        } else if (!have_near || g_rawcost <= nraw) {
            near = cur;
            nM = M;
            nK = Kk;
            nR = R;
            nraw = g_rawcost;
            have_near = 1;
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
# C engine 2 (new, bold): unstructured annealing on a bipartite graph with
# max degree d. The state is an arbitrary bipartite graph (no group
# structure). Cost = number of unordered vertex pairs at distance > D,
# computed with bitset ball expansion. Moves: double-edge swaps, filling a
# free slot pair, and moving one endpoint of an edge to a deficient vertex.
# Whenever cost reaches 0, the graph is snapshotted and one vertex is added
# to each side, so the search keeps growing from the last valid graph.
# ----------------------------------------------------------------------------

ANNEAL_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define HALF 2048
#define MD 64
#define SNAPCAP (HALF * MD)

static int d_ = 3, D_ = 3;
static int NA = 0;
static int deg[2 * HALF];
static int adj[2 * HALF * MD];
static uint64_t *R0 = NULL, *R1 = NULL;
static int W = 1;
static int snap[2 * SNAPCAP];
static int snap_n = 0, snap_m = 0;
static uint64_t rs = 88172645463325252ULL;
static int defA[HALF], defB[HALF];

typedef struct {
    int kind;
    int p[4];
} Move;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rand01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Compact index: A vertex i -> i, B vertex j -> NA + j. Vertex ids in
   adjacency: A i -> i, B j -> HALF + j. */
static inline int cidx(int id) { return id < HALF ? id : NA + (id - HALF); }
static inline int id_of(int t) { return t < NA ? t : HALF + (t - NA); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int find_nb(int v, int u) {
    int base = v * MD;
    for (int k = 0; k < deg[v]; k++)
        if (adj[base + k] == u) return k;
    return -1;
}

static void rep(int v, int old, int nw) {
    int k = find_nb(v, old);
    adj[v * MD + k] = nw;
}

static void addn(int v, int u) {
    adj[v * MD + deg[v]] = u;
    deg[v]++;
}

static void deln(int v, int u) {
    int k = find_nb(v, u);
    int last = --deg[v];
    adj[v * MD + k] = adj[v * MD + last];
}

static int isadj(int a, int b) { return find_nb(a, b) >= 0; }

/* Edges (x1,y1),(x2,y2) become (x1,y2),(x2,y1). Degrees unchanged. */
static void swap_move(int x1, int y1, int x2, int y2) {
    rep(x1, y1, y2);
    rep(y1, x1, x2);
    rep(x2, y2, y1);
    rep(y2, x2, x1);
}

static void apply_move(const Move *m) {
    switch (m->kind) {
    case 0:
        swap_move(m->p[0], m->p[1], m->p[2], m->p[3]);
        break;
    case 1:
        addn(m->p[0], m->p[1]);
        addn(m->p[1], m->p[0]);
        break;
    default: /* edge (f,w) becomes (f,w2) */
        rep(m->p[0], m->p[1], m->p[2]);
        deln(m->p[1], m->p[0]);
        addn(m->p[2], m->p[0]);
        break;
    }
}

static void undo_move(const Move *m) {
    switch (m->kind) {
    case 0:
        swap_move(m->p[0], m->p[3], m->p[2], m->p[1]);
        break;
    case 1:
        deln(m->p[0], m->p[1]);
        deln(m->p[1], m->p[0]);
        break;
    default:
        deln(m->p[2], m->p[0]);
        addn(m->p[1], m->p[0]);
        rep(m->p[0], m->p[2], m->p[1]);
        break;
    }
}

static void build_lists(int *nA_, int *nB_) {
    int nA = 0, nB = 0;
    for (int i = 0; i < NA; i++) {
        if (deg[i] < d_) defA[nA++] = i;
        if (deg[HALF + i] < d_) defB[nB++] = HALF + i;
    }
    *nA_ = nA;
    *nB_ = nB;
}

static int propose(Move *m, int nA, int nB) {
    int type = rint_(3);
    if (type == 0) {
        if (NA < 2) return 0;
        int a1 = rint_(NA), a2 = rint_(NA);
        if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) return 0;
        int b1 = adj[a1 * MD + rint_(deg[a1])];
        int b2 = adj[a2 * MD + rint_(deg[a2])];
        if (b1 == b2 || isadj(a1, b2) || isadj(a2, b1)) return 0;
        m->kind = 0;
        m->p[0] = a1;
        m->p[1] = b1;
        m->p[2] = a2;
        m->p[3] = b2;
        return 1;
    }
    if (nA == 0 || nB == 0) return 0;
    if (type == 1) {
        int a = defA[rint_(nA)], b = defB[rint_(nB)];
        if (isadj(a, b)) return 0;
        m->kind = 1;
        m->p[0] = a;
        m->p[1] = b;
        return 1;
    }
    int f, w2;
    if (rint_(2) == 0) {
        f = rint_(NA);
        w2 = defB[rint_(nB)];
    } else {
        f = HALF + rint_(NA);
        w2 = defA[rint_(nA)];
    }
    if (deg[f] == 0) return 0;
    int w = adj[f * MD + rint_(deg[f])];
    if (w == w2 || isadj(f, w2)) return 0;
    m->kind = 2;
    m->p[0] = f;
    m->p[1] = w;
    m->p[2] = w2;
    return 1;
}

/* Ball of radius D_ per vertex by bitset expansion. Returns the number of
   unordered pairs at distance > D_ (unreachable pairs included). */
static long long eval_cost(void) {
    int NT = 2 * NA;
    W = (NT + 63) >> 6;
    if (W < 1) W = 1;
    size_t sz = (size_t)NT * (size_t)W;
    memset(R0, 0, sizeof(uint64_t) * sz);
    for (int t = 0; t < NT; t++)
        R0[(size_t)t * W + (size_t)(t >> 6)] |= 1ULL << (t & 63);
    for (int it = 0; it < D_; it++) {
        for (int t = 0; t < NT; t++) {
            int id = id_of(t);
            uint64_t *row = R1 + (size_t)t * W;
            memcpy(row, R0 + (size_t)t * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[id]; k++) {
                int s = cidx(adj[id * MD + k]);
                const uint64_t *sr = R0 + (size_t)s * W;
                for (int w = 0; w < W; w++) row[w] |= sr[w];
            }
        }
        uint64_t *tmp = R0;
        R0 = R1;
        R1 = tmp;
    }
    long long pop = 0;
    for (int t = 0; t < NT; t++) {
        const uint64_t *row = R0 + (size_t)t * W;
        for (int w = 0; w < W; w++) pop += pc64(row[w]);
    }
    return ((long long)NT * (long long)NT - pop) / 2;
}

static void snapshot(void) {
    int n = 2 * NA;
    if (n <= snap_n) return;
    int m = 0;
    for (int i = 0; i < NA; i++) {
        for (int k = 0; k < deg[i]; k++) {
            int u = adj[i * MD + k];
            snap[2 * m] = i;
            snap[2 * m + 1] = NA + (u - HALF);
            m++;
        }
    }
    snap_n = n;
    snap_m = m;
}

static int grow(void) {
    if (NA >= HALF - 1) return 0;
    NA++;
    deg[NA - 1] = 0;
    deg[HALF + NA - 1] = 0;
    return 1;
}

static void random_fill(void) {
    for (long tries = 0; tries < 300000; tries++) {
        int nA, nB;
        build_lists(&nA, &nB);
        if (nA == 0 || nB == 0) break;
        int a = defA[rint_(nA)], b = defB[rint_(nB)];
        if (isadj(a, b)) continue;
        addn(a, b);
        addn(b, a);
    }
}

/* Loads a bipartite input graph into the A/B id scheme. Returns 1 on success. */
static int load_input(int n0, int m0, const int *eu, const int *ev) {
    int ok = 1;
    int *dg = calloc((size_t)n0, sizeof(int));
    int *off = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *pos = malloc(sizeof(int) * (size_t)(n0 + 1));
    int *nb = malloc(sizeof(int) * (size_t)(2 * m0 + 1));
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *q = malloc(sizeof(int) * (size_t)n0);
    int *mapid = malloc(sizeof(int) * (size_t)n0);
    if (!dg || !off || !pos || !nb || !col || !q || !mapid) return 0;
    for (int i = 0; i < m0; i++) {
        dg[eu[i]]++;
        dg[ev[i]]++;
    }
    for (int v = 0; v < n0; v++)
        if (dg[v] > MD) ok = 0;
    if (!ok) return 0;
    off[0] = 0;
    for (int v = 0; v < n0; v++) off[v + 1] = off[v] + dg[v];
    for (int v = 0; v < n0; v++) pos[v] = off[v];
    for (int i = 0; i < m0; i++) {
        nb[pos[eu[i]]++] = ev[i];
        nb[pos[ev[i]]++] = eu[i];
    }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = off[u]; k < off[u + 1]; k++) {
                int v = nb[k];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    q[tail++] = v;
                } else if (col[v] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) return 0;
    int ca = 0, cb = 0;
    for (int v = 0; v < n0; v++) {
        if (col[v] == 0) mapid[v] = ca++;
        else mapid[v] = HALF + (cb++);
    }
    if (ca >= HALF - 1 || cb >= HALF - 1) return 0;
    NA = ca > cb ? ca : cb;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        int a, b;
        if (col[u] == 0) {
            a = mapid[u];
            b = mapid[v];
        } else {
            a = mapid[v];
            b = mapid[u];
        }
        addn(a, b);
        addn(b, a);
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 1 || d_ > MD || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    R0 = calloc((size_t)2 * HALF * 64, sizeof(uint64_t));
    R1 = calloc((size_t)2 * HALF * 64, sizeof(uint64_t));
    if (!R0 || !R1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || m0 < 0) {
        n0 = 0;
        m0 = 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!eu || !ev) {
        printf("0 0\n");
        return 0;
    }
    int good = (n0 > 0 && m0 > 0);
    for (int i = 0; i < m0 && good; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            good = 0;
        } else if (eu[i] < 0 || ev[i] < 0 || eu[i] >= n0 || ev[i] >= n0 ||
                   eu[i] == ev[i]) {
            good = 0;
        }
    }
    int parsed = 0;
    if (good) parsed = load_input(n0, m0, eu, ev);
    if (parsed && m0 <= SNAPCAP) {
        snap_n = n0;
        snap_m = m0;
        for (int i = 0; i < m0; i++) {
            snap[2 * i] = eu[i];
            snap[2 * i + 1] = ev[i];
        }
    }
    if (!parsed) {
        NA = d_ + 1;
        for (int v = 0; v < 2 * HALF; v++) deg[v] = 0;
    }

    double t0 = now_s();
    double deadline = t0 + tl;
    const double T0 = 2.0, T1 = 0.1;

    random_fill();
    long long cur = eval_cost();
    int alive = 1;
    if (cur == 0) {
        snapshot();
        alive = grow();
        if (alive) cur = eval_cost();
    }

    long it = 0;
    double T = T0;
    while (alive) {
        if ((it & 15) == 0) {
            double now = now_s();
            if (now >= deadline) break;
            double frac = (now - t0) / tl;
            if (frac < 0) frac = 0;
            if (frac > 1) frac = 1;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int nA, nB;
        build_lists(&nA, &nB);
        Move mv;
        if (!propose(&mv, nA, nB)) continue;
        apply_move(&mv);
        long long nc = eval_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rand01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_move(&mv);
        }
        if (cur == 0) {
            snapshot();
            alive = grow();
            if (alive) cur = eval_cost();
        }
    }

    if (snap_n <= 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", snap_n, snap_m);
    for (int i = 0; i < snap_m; i++)
        printf("%d %d\n", snap[2 * i], snap[2 * i + 1]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _search(d, D, seed, budget, min_n):
    """One parent C search run. Returns (n, edges) if it produced a graph, else None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", min_n],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return None


def _anneal(d, D, seed, budget, graph):
    """One unstructured annealing run seeded with graph. Returns (n, edges) or None."""
    n, e = graph
    stdin = (n, e) if (n > 0 and e) else None
    try:
        out = lib.run_c(ANNEAL_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=stdin, timeout=budget + 3.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > 0 and lib.is_valid(n2, e2, d, D):
            return n2, e2
    except Exception:
        pass
    return None


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
        total = deadline - time.monotonic() - 1.5
        if total >= 4.0:
            # Stage 1: structured bi-Cayley search gives a strong valid start.
            res1 = _search(d, D, seed, 0.40 * total, best_n)
            if res1 is not None:
                consider(*res1)
            # Stage 2: unstructured annealing grows from the best valid graph.
            remaining = deadline - time.monotonic() - 1.5
            if remaining >= 4.0:
                res2 = _anneal(d, D, seed + 104729, remaining, best)
                if res2 is not None:
                    consider(*res2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
