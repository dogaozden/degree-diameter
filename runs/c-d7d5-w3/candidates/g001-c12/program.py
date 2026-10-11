import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged from the parent): PG(2,q) and W(q) incidence graphs.
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
# Stage 1 C engine: bi-Cayley breakout search (parent engine, unchanged).
# It produces a regular, valid start graph of order above best_n.
# ----------------------------------------------------------------------------

BICAYLEY_SOURCE = r'''
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
            /* Mostly K = 1 (bi-Cayley), sometimes K = 2. The window above
               best_n widens with consecutive failures, capped at g0/3. */
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
# Stage 2 C engine (new): simulated annealing on general d-regular bipartite
# graphs. The state is an arbitrary bipartite graph with all degrees d. Moves
# are 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1), which keep degrees and
# bipartiteness. The cost is the number of vertex pairs at distance > D,
# computed exactly with bitset BFS. Whenever the cost reaches 0 the graph is
# snapshotted and grown by two vertices: a new A vertex y and a new B vertex x
# take over d disjoint edges (a_k,b_k) as a_k-x and y-b_k. Annealing then
# repairs the new defects. Every returned graph is valid, and the best
# snapshot is printed at the end.
# ----------------------------------------------------------------------------

ANNEAL_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW (MAXN / 64)
#define MAXDEG 32
#define MAXE (MAXN * MAXDEG / 2 + 64)
#define STALL 4000

static int dd, DD, N, E;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int side[MAXN];
static uint64_t AM[MAXN][MAXW];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int ea[MAXE], eb[MAXE];
static int sN = 0, sE = 0;
static int sEa[MAXE], sEb[MAXE];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double unif(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
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

static int has_edge(int a, int b) { return (int)((AM[a][b >> 6] >> (b & 63)) & 1ULL); }
static void set_bit(int a, int b) { AM[a][b >> 6] |= 1ULL << (b & 63); }
static void clr_bit(int a, int b) { AM[a][b >> 6] &= ~(1ULL << (b & 63)); }

static void add_adj(int v, int u) { adj[v][deg[v]++] = u; }
static void del_adj(int v, int u) {
    for (int k = 0; k < deg[v]; k++)
        if (adj[v][k] == u) {
            adj[v][k] = adj[v][--deg[v]];
            return;
        }
}
static void add_edge(int a, int b) {
    set_bit(a, b);
    set_bit(b, a);
    add_adj(a, b);
    add_adj(b, a);
}
static void del_edge(int a, int b) {
    clr_bit(a, b);
    clr_bit(b, a);
    del_adj(a, b);
    del_adj(b, a);
}
static void clear_graph(void) {
    memset(AM, 0, sizeof(AM));
    memset(deg, 0, sizeof(deg));
}
static void rebuild_edges(void) {
    E = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < deg[v]; k++) {
            ea[E] = v;
            eb[E] = adj[v][k];
            E++;
        }
    }
}

static int color_graph(int n) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    q[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* 2-switch on edge slots i=(a1,b1) and j=(a2,b2) -> (a1,b2),(a2,b1).
   Applying it again to the same slots undoes it. */
static int twoswitch(int i, int j) {
    int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    del_edge(a1, b1);
    del_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    ea[i] = a1;
    eb[i] = b2;
    ea[j] = a2;
    eb[j] = b1;
    return 1;
}

/* Number of unordered vertex pairs at distance > DD (0 means valid). */
static long long evaluate(void) {
    int w = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)w);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int t = 0; t < w; t++) nxt[v][t] |= src[t];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int t = 0; t < w; t++) c += popc(cur[v][t]);
        unr += N - c;
    }
    return unr / 2;
}

static void save_snapshot(void) {
    sN = N;
    sE = E;
    memcpy(sEa, ea, sizeof(int) * (size_t)E);
    memcpy(sEb, eb, sizeof(int) * (size_t)E);
}

static void restore_snapshot(void) {
    clear_graph();
    N = sN;
    for (int i = 0; i < sE; i++) add_edge(sEa[i], sEb[i]);
    rebuild_edges();
}

/* Add two vertices y (side A) and x (side B) with degree dd, by taking dd
   disjoint edges (a_k,b_k) and replacing them with a_k-x and y-b_k. */
static int grow(void) {
    if (N + 2 > MAXN || E < dd) return 0;
    int ca[MAXDEG], cb[MAXDEG];
    int cnt = 0;
    for (int att = 0; att < 200000 && cnt < dd; att++) {
        int i = rint_(E);
        int a = ea[i], b = eb[i];
        int ok = 1;
        for (int k = 0; k < cnt; k++)
            if (ca[k] == a || cb[k] == b) {
                ok = 0;
                break;
            }
        if (ok) {
            ca[cnt] = a;
            cb[cnt] = b;
            cnt++;
        }
    }
    if (cnt < dd) return 0;
    int y = N, x = N + 1;
    side[y] = 0;
    side[x] = 1;
    for (int k = 0; k < dd; k++) del_edge(ca[k], cb[k]);
    N += 2;
    for (int k = 0; k < dd; k++) {
        add_edge(ca[k], x);
        add_edge(y, cb[k]);
    }
    rebuild_edges();
    return 1;
}

int main(int argc, char **argv) {
    dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 5.0;
    if (dd < 1 || dd > MAXDEG || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    clear_graph();
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= dd || deg[v] >= dd) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++)
        if (deg[v] != dd) {
            printf("0 0\n");
            return 0;
        }
    if (!color_graph(n)) {
        printf("0 0\n");
        return 0;
    }
    rebuild_edges();

    double t0 = now_s();
    double deadline = t0 + tl;
    double total = tl > 1e-3 ? tl : 1e-3;
    long long cur = evaluate();
    long long bestc = cur, since = 0;

    while (1) {
        double t = now_s();
        if (t >= deadline) break;
        if (cur == 0) {
            if (N > sN) save_snapshot();
            if (!grow()) break;
            cur = evaluate();
            bestc = cur;
            since = 0;
            continue;
        }
        if (E < 2) break;
        int i = rint_(E), j = rint_(E);
        if (i == j) continue;
        if (!twoswitch(i, j)) continue;
        long long c = evaluate();
        double frac = (deadline - t) / total;
        double T = 0.3 + 2.0 * frac;
        int acc;
        if (c <= cur) acc = 1;
        else acc = unif() < exp(-(double)(c - cur) / T);
        if (acc) cur = c;
        else twoswitch(i, j);
        if (cur < bestc) {
            bestc = cur;
            since = 0;
        } else {
            since++;
        }
        if (since > STALL) {
            restore_snapshot();
            cur = evaluate();
            bestc = cur;
            since = 0;
        }
    }

    if (sN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", sN, sE);
    for (int i = 0; i < sE; i++) printf("%d %d\n", sEa[i], sEb[i]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(3.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + total

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular, bipartite, and has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (same early exits as the parent).
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
        # Stage 1: bi-Cayley breakout search gives a strong regular start.
        seed_graph = None
        b1 = 0.4 * (deadline - time.monotonic())
        if b1 >= 2.0:
            try:
                out = lib.run_c(BICAYLEY_SOURCE, [d, D, seed, f"{b1:.2f}", best_n],
                                timeout=b1 + 10.0)
                n1, e1 = lib.parse_graph_text(out)
                if lib.is_valid(n1, e1, d, D) and _is_regular(n1, e1, d):
                    seed_graph = (n1, e1)
                consider(n1, e1)
            except Exception:
                pass

        # Stage 2: annealing with 2-switches and vertex growth, started from
        # the stage-1 graph (or K_{d,d} if stage 1 failed).
        remaining = deadline - time.monotonic() - 1.0
        if remaining >= 2.0:
            start_graph = seed_graph if seed_graph is not None else lib.haar_graph(d, range(d))
            try:
                out = lib.run_c(ANNEAL_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                                stdin_graph=start_graph, timeout=remaining + 10.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
