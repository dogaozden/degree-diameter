import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions.
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
# Engine 1 (new): bi-Cayley lift search by simulated annealing.
# Base: K left and K right vertices (K = 1..4), Dd layers. Each layer is a
# perfect matching P[l] (a permutation) with a voltage S[l][i] in a group of
# order GG = m*k (semidirect product Z_m x| Z_k). Cost = unreached (source,
# vertex) pairs over the 2K base sources plus a penalty for repeated darts.
# Moves: change one voltage, or swap two entries of one layer's matching.
# The group acts by left multiplication, so the sources cover all pairs.
# ----------------------------------------------------------------------------

SA_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXK 4
#define MAXV 4096
#define PEN 50
#define ITERS 40000L

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

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int adjv[MAXV * MAXD];
static int acnt[MAXV];
static int visst[MAXV];
static int vstamp = 0;
static int bfsq[MAXV];

static long long energy(const Cfg *c) {
    int K = c->K, G = c->G, N = 2 * K * G;
    for (int v = 0; v < N; v++) acnt[v] = 0;
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = c->P[l][i], s = c->S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                adjv[a * Dd + acnt[a]++] = b;
                adjv[b * Dd + acnt[b]++] = a;
            }
        }
    }
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < Dd; l1++)
            for (int l2 = l1 + 1; l2 < Dd; l2++)
                if (c->P[l1][i] == c->P[l2][i] && c->S[l1][i] == c->S[l2][i])
                    dup++;

    long long raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        vstamp++;
        int h = 0, t = 0;
        int src = r * G;
        visst[src] = vstamp;
        bfsq[t++] = src;
        for (int lvl = 0; lvl < DD; lvl++) {
            int end = t;
            if (h == end) break;
            while (h < end) {
                int u = bfsq[h++];
                for (int q = 0; q < acnt[u]; q++) {
                    int v = adjv[u * Dd + q];
                    if (visst[v] != vstamp) {
                        visst[v] = vstamp;
                        bfsq[t++] = v;
                    }
                }
            }
        }
        raw += N - t;
    }
    return raw + (long long)PEN * dup;
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

/* Simulated annealing on the current group. Returns 1 if cost 0 is reached. */
static int anneal(Cfg *c, long iters, double T0, double T1) {
    long long E = energy(c);
    for (long it = 0; it < iters && E > 0; it++) {
        if ((it & 63) == 0 && now_s() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rint_(Dd), i = rint_(c->K);
        int kind = (c->K >= 2 && rint_(3) == 0);
        int oldS = 0, i2 = 0;
        if (kind) {
            i2 = rint_(c->K - 1);
            if (i2 >= i) i2++;
            int t = c->P[l][i];
            c->P[l][i] = c->P[l][i2];
            c->P[l][i2] = t;
        } else {
            oldS = c->S[l][i];
            c->S[l][i] = rint_(GG);
        }
        long long E2 = energy(c);
        long long dE = E2 - E;
        if (dE <= 0 || rnd01() < exp(-(double)dE / T)) {
            E = E2;
        } else {
            if (kind) {
                int t = c->P[l][i];
                c->P[l][i] = c->P[l][i2];
                c->P[l][i2] = t;
            } else {
                c->S[l][i] = oldS;
            }
        }
    }
    return E == 0;
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
    Dd = argc > 1 ? atoi(argv[1]) : 7;
    DD = argc > 2 ? atoi(argv[2]) : 5;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int min_n = argc > 5 ? atoi(argv[5]) : 0;

    if (Dd < 1 || Dd > MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 4242ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    deadline = now_s() + tl;
    int best_n = min_n;
    int have = 0;
    int bM = 1, bK = 1, bR = 1;
    Cfg best, cur;
    memset(&best, 0, sizeof(best));
    memset(&cur, 0, sizeof(cur));

    while (now_s() < deadline) {
        int rr = rint_(100);
        int K = rr < 25 ? 1 : (rr < 60 ? 2 : (rr < 85 ? 3 : 4));
        long long g0 = (long long)best_n / (2 * K) + 1;
        long long span = g0 / 40 + 3;
        long long g = g0 + (long long)rint_((int)span);

        int M, Kk, R;
        sample_group(g, &M, &Kk, &R);
        set_group(M, Kk, R);
        if (GG > MAXV) continue;
        int N = 2 * K * GG;
        if (N <= best_n || N > MAXV) continue;

        cur.K = K;
        cur.G = GG;
        random_cfg(&cur);
        if (anneal(&cur, ITERS, 2.0, 0.2)) {
            best_n = N;
            best = cur;
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
    int K = best.K, G = best.G;
    int n = 2 * K * G;
    long m = (long)Dd * K * G;
    printf("%d %ld\n", n, m);
    for (int l = 0; l < Dd; l++) {
        for (int i = 0; i < K; i++) {
            int j = best.P[l][i], s = best.S[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Engine 2: vertex growth by edge splitting, then repair.
#
# Input: a valid bipartite graph with max degree d (from engine 1 or a
# fallback). Loop:
#   * if the current graph has diameter <= D (cost 0), save it and grow:
#     add one left vertex a and one right vertex b. Pick d edges (x, y)
#     with distinct endpoints; replace each by (x, a) and add (b, y). Degrees
#     are preserved, a and b get degree d, and the graph gains 2 vertices.
#   * otherwise anneal on the number of unordered pairs at distance > D,
#     using degree-preserving double-edge switches.
# Distances come from bitset balls of radius D. Only saved graphs with cost 0
# are printed, so the output is valid whenever it is non-empty.
# ----------------------------------------------------------------------------

EXT_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2600
#define WMAX ((MAXN + 63) / 64)

static uint64_t rs = 0x2545F4914F6CDD1DULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int Dd = 3, DD = 3;
static int N = 0, M = 0;
static int *ex, *ey;          /* edge k: ex[k] is a right vertex, ey[k] a left vertex */
static int *nb, *ncnt;
static char *adj;             /* MAXN x MAXN adjacency matrix */
static uint64_t *RA, *RB;
static int stx[MAXN], sty[MAXN], stamp = 0;
static int *bestEx, *bestEy;
static int bestN = 0, bestM = 0;
static long long cur_bad = 0;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void aset(int x, int y, char v) {
    adj[(size_t)x * MAXN + y] = v;
    adj[(size_t)y * MAXN + x] = v;
}

static void build_nb(void) {
    for (int v = 0; v < N; v++) ncnt[v] = 0;
    for (int k = 0; k < M; k++) {
        int x = ex[k], y = ey[k];
        nb[x * Dd + ncnt[x]++] = y;
        nb[y * Dd + ncnt[y]++] = x;
    }
}

/* Number of unordered vertex pairs at distance > DD (0 means valid). */
static long long eval_bad(void) {
    int W = (N + 63) >> 6;
    build_nb();
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int t = 0; t < ncnt[v]; t++) {
                const uint64_t *u = cur + (size_t)nb[v * Dd + t] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long reached = 0;
    size_t total_words = (size_t)N * (size_t)W;
    for (size_t i = 0; i < total_words; i++) reached += pc64(cur[i]);
    long long total = (long long)N * (long long)N;
    return (total - reached) / 2;
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(bestEx, ex, sizeof(int) * (size_t)M);
    memcpy(bestEy, ey, sizeof(int) * (size_t)M);
}

/* One degree-preserving double-edge switch, accepted by Metropolis rule. */
static void move(double T) {
    int a = rint_(M), b = rint_(M);
    if (a == b) return;
    int x1 = ex[a], y1 = ey[a], x2 = ex[b], y2 = ey[b];
    if (x1 == x2 || y1 == y2) return;
    if (adj[(size_t)x1 * MAXN + y2] || adj[(size_t)x2 * MAXN + y1]) return;
    aset(x1, y1, 0);
    aset(x2, y2, 0);
    aset(x1, y2, 1);
    aset(x2, y1, 1);
    ex[a] = x1; ey[a] = y2;
    ex[b] = x2; ey[b] = y1;
    long long nbad = eval_bad();
    long long delta = nbad - cur_bad;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        cur_bad = nbad;
        return;
    }
    aset(x1, y2, 0);
    aset(x2, y1, 0);
    aset(x1, y1, 1);
    aset(x2, y2, 1);
    ex[a] = x1; ey[a] = y1;
    ex[b] = x2; ey[b] = y2;
}

/* Add a left vertex a = N and a right vertex b = N+1 by splitting Dd edges. */
static int grow(void) {
    if (N + 2 > MAXN) return 0;
    if (M < Dd) return 0;
    int a = N, b = N + 1;
    int chosen[64];
    int cnt = 0;
    stamp++;
    for (int tries = 0; tries < 20000 && cnt < Dd; tries++) {
        int k = rint_(M);
        int x = ex[k], y = ey[k];
        if (stx[x] == stamp || sty[y] == stamp) continue;
        stx[x] = stamp;
        sty[y] = stamp;
        chosen[cnt++] = k;
    }
    if (cnt < Dd) return 0;
    N += 2;
    for (int i = 0; i < cnt; i++) {
        int k = chosen[i];
        int x = ex[k], y = ey[k];
        aset(x, y, 0);
        ex[k] = x; ey[k] = a;
        aset(x, a, 1);
        ex[M] = b; ey[M] = y;
        aset(b, y, 1);
        M++;
    }
    return 1;
}

int main(int argc, char **argv) {
    Dd = argc > 1 ? atoi(argv[1]) : 3;
    DD = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 5.0;
    if (Dd < 1 || Dd > 64 || DD < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();
    double dl = now_s() + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 2 || m < 0 || m > n * Dd) {
        printf("0 0\n");
        return 0;
    }
    adj = calloc((size_t)MAXN * MAXN, 1);
    int *iu = malloc(sizeof(int) * (size_t)(m + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m + 1));
    int *dg = calloc((size_t)n, sizeof(int));
    if (!adj || !iu || !iv || !dg) {
        printf("0 0\n");
        return 0;
    }
    int ok = 1;
    for (int k = 0; k < m && ok; k++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
        } else if (u < 0 || v < 0 || u >= n || v >= n || u == v) {
            ok = 0;
        } else if (adj[(size_t)u * MAXN + v]) {
            ok = 0;
        } else {
            iu[k] = u;
            iv[k] = v;
            dg[u]++;
            dg[v]++;
            if (dg[u] > Dd || dg[v] > Dd) ok = 0;
            aset(u, v, 1);
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the input (bipartition). */
    int *off = calloc((size_t)n + 1, sizeof(int));
    int *pos = malloc(sizeof(int) * (size_t)n);
    int *csr = malloc(sizeof(int) * (size_t)(2 * m + 1));
    int *col = malloc(sizeof(int) * (size_t)n);
    int *q = malloc(sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) off[v + 1] = off[v] + dg[v];
    for (int v = 0; v < n; v++) pos[v] = off[v];
    for (int k = 0; k < m; k++) {
        csr[pos[iu[k]]++] = iv[k];
        csr[pos[iv[k]]++] = iu[k];
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail && ok) {
            int u = q[head++];
            for (int t = off[u]; t < off[u + 1]; t++) {
                int w = csr[t];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    q[tail++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    ex = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    ey = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    nb = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    ncnt = malloc(sizeof(int) * (size_t)MAXN);
    RA = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    RB = malloc(sizeof(uint64_t) * (size_t)MAXN * WMAX);
    bestEx = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    bestEy = malloc(sizeof(int) * (size_t)MAXN * (size_t)Dd);
    if (!ex || !ey || !nb || !ncnt || !RA || !RB || !bestEx || !bestEy) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    M = m;
    for (int k = 0; k < m; k++) {
        int u = iu[k], v = iv[k];
        if (col[u] == 1) {
            ex[k] = u;
            ey[k] = v;
        } else {
            ex[k] = v;
            ey[k] = u;
        }
    }

    cur_bad = eval_bad();
    double T = 0.5;
    if (M >= 2) {
        while (now_s() < dl) {
            if (cur_bad == 0) {
                save_best();
                if (!grow()) break;
                cur_bad = eval_bad();
                continue;
            }
            for (int it = 0; it < 200 && cur_bad != 0; it++) move(T);
            if (cur_bad == 0) save_best();
        }
    }
    if (cur_bad == 0 && bestN != N) save_best();

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int k = 0; k < bestM; k++) printf("%d %d\n", bestEx[k], bestEy[k]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue.
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

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    if d < 3 or D < 3:
        return best

    # Phase 1: simulated-annealing lift search over base sizes 1..4 (engine 1).
    remaining = deadline - time.monotonic()
    frac = 0.7 if D >= 5 else 0.9
    a_budget = remaining * frac - 1.0
    if a_budget >= 2.0:
        try:
            out = lib.run_c(SA_SOURCE, [d, D, seed, f"{a_budget:.2f}", best[0]],
                            timeout=a_budget + 10.0)
            n1, e1 = lib.parse_graph_text(out)
            consider(n1, e1)
        except Exception:
            pass

    # Phase 2: grow the best valid graph by edge splitting, then repair (engine 2).
    remaining = deadline - time.monotonic()
    b_budget = remaining - 2.0
    if b_budget >= 2.0 and best[0] >= 4:
        try:
            out = lib.run_c(EXT_SOURCE, [d, D, seed, f"{b_budget:.2f}"],
                            stdin_graph=best, timeout=b_budget + 10.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
