import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: simulated annealing over the voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Base graph: K vertices per
# side, DEG layers, each layer a permutation of 0..K-1. Cost = unreached
# (representative, vertex) pairs within DIAM steps + duplicate penalty.
# Later anneals restart from the best state with a random kick (reheating).
# Usage: prog d D K m k2 r seed slice_seconds. Prints "n m" + edges, or "0 0".
# ----------------------------------------------------------------------------

C_ANNEAL = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 60) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
            for (int l = 0; l < DEG; l++) {
                for (int i = 0; i < K; i++) p[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    dI[l * K + i] = i;
                    dJ[l * K + i] = p[i];
                }
            }
            for (int e = 0; e < NE; e++) {
                dS[e] = rndint(G);
                set_perm(e);
            }
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B: vertex growth by edge splitting, then repair.
# Input: a valid bipartite graph with max degree d. While the current graph
# has diameter <= D, save it and add one left and one right vertex by
# splitting d edges with distinct endpoints (degrees preserved, +2 vertices).
# Otherwise anneal the number of pairs at distance > D with degree-preserving
# double-edge switches. Only saved graphs with cost 0 are printed.
# ----------------------------------------------------------------------------

C_GROW = r'''
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
static int *ex, *ey;
static int *nb, *ncnt;
static char *adj;
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
# Exact / safe constructions.
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
# Group sampling and the driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

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

    # Alternate: voltage annealing (new lifts) and vertex growth (grows the best).
    failures = 0
    grow_turn = False
    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(remaining - 1.0, 10.0)
        if not grow_turn:
            k = rng.choice([1, 1, 2, 2, 3])
            base = best[0] // (2 * k)
            target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            try:
                out = lib.run_c(
                    C_ANNEAL,
                    [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                failures += 1
        else:
            if best[0] >= 4:
                try:
                    out = lib.run_c(
                        C_GROW,
                        [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                        stdin_graph=best,
                        timeout=slice_s + 10.0,
                    )
                    n, e = lib.parse_graph_text(out)
                    consider(n, e)
                except (RuntimeError, ValueError):
                    failures += 1
        grow_turn = not grow_turn

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
