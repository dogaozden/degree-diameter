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
# Stage 1 C engine (lift search): bi-Cayley search with breakout local search,
# coordinate polish, and near-miss iterated local search. Unchanged parent engine.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r'''
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
    int fails = 0;
    Cfg cur, best_cfg, near;
    memset(&cur, 0, sizeof(cur));
    memset(&best_cfg, 0, sizeof(best_cfg));
    memset(&near, 0, sizeof(near));

    int have_near = 0;
    int nM = 1, nK = 1, nR = 1;
    long long nraw = 0;

    while (now_s() < deadline) {
        int K, M, Kk, R;
        int from_near = have_near && (rint_(100) < NEAR_PCT);
        if (from_near) {
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
# Stage 2 C engine (growth and repair). Bold change: instead of searching for
# a whole new group lift, take a valid graph, add a vertex pair (one per side)
# by edge subdivision-style insertion, and then repair the bad pairs by
# simulated annealing over degree-preserving bipartite 2-switches. The cost is
# the number of vertex pairs at distance more than D, counted with bitsets.
# Every returned graph is valid by construction (checked again in Python).
# ----------------------------------------------------------------------------

REPAIR_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

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

static int DEG = 3, DIAM = 3, CAP = 0, WCAP = 0;
static int N = 0, M = 0;
static int *side, *dg, *adj, *EA, *EB;
static int *bEA, *bEB;
static int bN = 0, bM = 0;
static unsigned char *mat;
static uint64_t *bufA, *bufB;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0FULL * 0x0101010101010101ULL / 0x0101010101010101ULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM. */
static long long cost_eval(void) {
    int Wc = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * WCAP;
        memset(r, 0, sizeof(uint64_t) * (size_t)Wc);
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * WCAP;
            uint64_t *self = cur + (size_t)v * WCAP;
            memcpy(o, self, sizeof(uint64_t) * (size_t)Wc);
            for (int k = 0; k < dg[v]; k++) {
                uint64_t *r = cur + (size_t)adj[v * DEG + k] * WCAP;
                for (int w = 0; w < Wc; w++) o[w] |= r[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        uint64_t *r = cur + (size_t)v * WCAP;
        int c = 0;
        for (int w = 0; w < Wc; w++) c += popc(r[w]);
        bad += N - c;
    }
    return bad / 2;
}

static void set_nb(int x, int old, int nw) {
    for (int k = 0; k < dg[x]; k++) {
        if (adj[x * DEG + k] == old) {
            adj[x * DEG + k] = nw;
            return;
        }
    }
}

static void add_nb(int x, int y) {
    adj[x * DEG + dg[x]] = y;
    dg[x]++;
}

static void set_edge(int x, int y, int v) {
    mat[x * CAP + y] = (unsigned char)v;
    mat[y * CAP + x] = (unsigned char)v;
}

/* Edges e1=(a1,b1), e2=(a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static int swap_ok(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    return a1 != a2 && b1 != b2 && !mat[a1 * CAP + b2] && !mat[a2 * CAP + b1];
}

static void swap2(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    set_edge(a1, b1, 0);
    set_edge(a2, b2, 0);
    set_edge(a1, b2, 1);
    set_edge(a2, b1, 1);
    set_nb(a1, b1, b2);
    set_nb(b1, a1, a2);
    set_nb(a2, b2, b1);
    set_nb(b2, a2, a1);
    EB[e1] = b2;
    EB[e2] = b1;
}

/* Add a new A vertex x and B vertex y, keeping all degrees <= DEG. */
static int grow_pair(void) {
    if (N + 2 > CAP || M < 1) return 0;
    int x = N, y = N + 1;
    N += 2;
    side[x] = 0;
    side[y] = 1;
    dg[x] = 0;
    dg[y] = 0;

    int e = rint_(M);
    int a = EA[e], b = EB[e];
    /* Edge (a,b) becomes (a,y); new edges (x,b) and (x,y). */
    set_edge(a, b, 0);
    set_nb(a, b, y);
    set_nb(b, a, x);
    EB[e] = y;
    set_edge(a, y, 1);
    EA[M] = x;
    EB[M] = b;
    M++;
    set_edge(x, b, 1);
    EA[M] = x;
    EB[M] = y;
    M++;
    set_edge(x, y, 1);
    add_nb(x, b);
    add_nb(x, y);
    add_nb(y, a);
    add_nb(y, x);

    /* Fill the remaining degree of x and y: (p,q) becomes (p,y), new (x,q). */
    for (int t = 2; t < DEG; t++) {
        long long tries = 0;
        while (1) {
            int f = rint_(M);
            int p = EA[f], q = EB[f];
            tries++;
            if (p == x || q == y) continue;
            if (mat[x * CAP + q] || mat[p * CAP + y]) continue;
            set_edge(p, q, 0);
            set_nb(p, q, y);
            set_nb(q, p, x);
            EB[f] = y;
            set_edge(p, y, 1);
            EA[M] = x;
            EB[M] = q;
            M++;
            set_edge(x, q, 1);
            add_nb(y, p);
            add_nb(x, q);
            break;
        }
    }
    return 1;
}

static void save_best(void) {
    for (int e = 0; e < M; e++) {
        bEA[e] = EA[e];
        bEB[e] = EB[e];
    }
    bM = M;
    bN = N;
}

int main(int argc, char **argv) {
    DEG = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double budget = argc > 4 ? atof(argv[4]) : 10.0;
    int cap_arg = argc > 5 ? atoi(argv[5]) : 0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || m0 < 1 || DEG < 3 || DIAM < 1 || n0 > 4000) {
        printf("0 0\n");
        return 0;
    }
    CAP = cap_arg > n0 + 2 ? cap_arg : n0 + 2;
    if (CAP > 4002) {
        printf("0 0\n");
        return 0;
    }
    WCAP = (CAP + 63) / 64;
    side = calloc((size_t)CAP, sizeof(int));
    dg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG, sizeof(int));
    EA = calloc((size_t)CAP * DEG, sizeof(int));
    EB = calloc((size_t)CAP * DEG, sizeof(int));
    bEA = calloc((size_t)CAP * DEG, sizeof(int));
    bEB = calloc((size_t)CAP * DEG, sizeof(int));
    mat = calloc((size_t)CAP * CAP, 1);
    bufA = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    bufB = calloc((size_t)CAP * WCAP, sizeof(uint64_t));
    int *queue = calloc((size_t)CAP, sizeof(int));
    if (!side || !dg || !adj || !EA || !EB || !bEA || !bEB || !mat || !bufA || !bufB || !queue) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || u >= N || v < 0 || v >= N || u == v || dg[u] >= DEG || dg[v] >= DEG
            || mat[u * CAP + v]) {
            printf("0 0\n");
            return 0;
        }
        set_edge(u, v, 1);
        add_nb(u, v);
        add_nb(v, u);
    }

    /* Two-colour the input; reject if it is not bipartite. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int u = queue[head++];
            for (int k = 0; k < dg[u]; k++) {
                int w = adj[u * DEG + k];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    queue[tail++] = w;
                } else if (side[w] == side[u]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }
    M = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] != 0) continue;
        for (int k = 0; k < dg[v]; k++) {
            EA[M] = v;
            EB[M] = adj[v * DEG + k];
            M++;
        }
    }

    double t0 = now_s();
    double tend = t0 + budget;
    const int phase_len = 6000;
    const double T0 = 1.2, T1 = 0.03;
    int phase_iter = 0;

    long long cur = cost_eval();
    if (cur == 0) save_best();

    while (1) {
        if (now_s() >= tend) break;
        if (cur == 0) {
            save_best();
            if (!grow_pair()) break;
            cur = cost_eval();
            phase_iter = 0;
            continue;
        }
        phase_iter = (phase_iter + 1) % phase_len;
        if (M < 2) break;
        int e1 = rint_(M), e2 = rint_(M);
        if (e1 == e2 || !swap_ok(e1, e2)) continue;
        swap2(e1, e2);
        long long c2 = cost_eval();
        long long delta = c2 - cur;
        double frac = (double)phase_iter / (double)phase_len;
        double T = T0 * pow(T1 / T0, frac);
        if (delta <= 0 || rfloat() < exp(-(double)delta / T)) {
            cur = c2;
        } else {
            swap2(e1, e2);
        }
    }
    if (cur == 0) save_best();

    if (bN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bN, bM);
    for (int e = 0; e < bM; e++) printf("%d %d\n", bEA[e], bEB[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then lift search, then growth and repair.
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
        # Stage 1: lift search, a shorter share of the budget.
        remaining = deadline - time.monotonic()
        lift_budget = 0.45 * remaining - 0.5
        if lift_budget >= 2.0:
            try:
                out = lib.run_c(LIFT_SOURCE, [d, D, seed, f"{lift_budget:.2f}", best_n],
                                timeout=lift_budget + 4.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

        # Stage 2: grow the current best by vertex pairs and repair with annealing.
        rep_budget = deadline - time.monotonic() - 1.0
        cap = min(lib.moore_bound(d, D), 4000) + 2
        if rep_budget >= 2.0 and best_n + 2 <= cap:
            try:
                out = lib.run_c(REPAIR_SOURCE, [d, D, seed + 1, f"{rep_budget:.2f}", cap],
                                stdin_graph=best, timeout=rep_budget + 4.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
