import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baseline families (safe fallbacks, unchanged from the parents).
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
# Main search in C: bi-Cayley lifts over G = Z_m x| Z_k2 with K base vertices
# per side and d layers. Layer l is a permutation perm[l] of the K base
# vertices plus one voltage vol[l][i] per dart, so every vertex has degree d.
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (K+j)*G + h. Dart (l,i) joins
# A_{i,g} to B_{perm[l][i], g*vol[l][i]}. Left multiplication is an
# automorphism, so BFS from the 2K identity representatives decides diameter.
#
# Annealing minimises (unreached rep-vertex pairs) + penalty * (duplicate
# darts). Each trial targets an order just above the best found so far, with
# group orders sampled from divisors. The engine prints the best valid lift.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXDEG 64
#define MAXK 8
#define MAXK2 64
#define PEN 1000LL
#define ITERS 6000

static int DEG = 3, DIA = 3;
static double DEADLINE = 0.0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* group Z_m x| Z_k2, element (a,b) coded a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) */
static int GM = 1, GK = 1, GG = 1;
static long long PW[MAXK2];

static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    long long na = ((long long)a + PW[b] * (long long)c) % GM;
    int nb = (b + e) % GK;
    return (int)na * GK + nb;
}

static void set_group(int m, int k2, int r) {
    GM = m;
    GK = k2;
    GG = m * k2;
    PW[0] = 1 % m;
    for (int b = 1; b < k2; b++) PW[b] = (PW[b - 1] * r) % m;
}

static long long pmodll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m <= 2 || rndint(4) == 0) return 1;
    for (int t = 0; t < 200; t++) {
        int r = 2 + rndint(m - 2);
        if (gcdi(r, m) == 1 && pmodll(r, k2, m) == 1 % m) return r;
    }
    return 1;
}

/* lift state */
static int KL = 1;
static int perm[MAXDEG][MAXK], vol[MAXDEG][MAXK];
static int sperm[MAXDEG][MAXK], svol[MAXDEG][MAXK];
static int capN = 0;
static int *nbr = NULL, *ncnt = NULL, *vis = NULL, *que = NULL;
static int stamp = 0;

static void ensure_cap(int N) {
    if (N <= capN) return;
    free(nbr); free(ncnt); free(vis); free(que);
    capN = N;
    nbr = malloc(sizeof(int) * (size_t)N * MAXDEG);
    ncnt = malloc(sizeof(int) * (size_t)N);
    vis = calloc((size_t)N, sizeof(int));
    que = malloc(sizeof(int) * (size_t)N);
    stamp = 0;
    if (!nbr || !ncnt || !vis || !que) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
}

static long long evalcost(void) {
    int K = KL, d = DEG, G = GG, N = 2 * K * G;
    long long dup = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (perm[l1][i] == perm[l2][i] && vol[l1][i] == vol[l2][i]) dup++;

    memset(ncnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int j = perm[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + gmul(g, s);
                nbr[a * d + ncnt[a]++] = b;
                nbr[b * d + ncnt[b]++] = a;
            }
        }
    }

    long long total = 0;
    for (int q = 0; q < 2 * K; q++) {
        int src = q * G;  /* identity representative of block q */
        stamp++;
        int head = 0, tail = 0;
        que[tail++] = src;
        vis[src] = stamp;
        for (int lev = 0; lev < DIA && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                for (int t = 0; t < d; t++) {
                    int v = nbr[u * d + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total + PEN * dup;
}

static void init_state(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < KL; i++) perm[l][i] = i;
        for (int i = KL - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < KL; i++) vol[l][i] = rndint(GG);
    }
}

/* returns 1 if a zero-cost lift was reached, 0 if not, -1 on timeout */
static int anneal(int iters, double T0, double deadline) {
    init_state();
    long long cur = evalcost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && now_s() > deadline) return -1;
        int swap_kind = (KL >= 2 && rndint(4) == 0);
        int l = rndint(DEG), i = rndint(KL), i2 = 0, oldv = 0;
        if (swap_kind) {
            i2 = rndint(KL - 1);
            if (i2 >= i) i2++;
            int t = perm[l][i];
            perm[l][i] = perm[l][i2];
            perm[l][i2] = t;
        } else {
            oldv = vol[l][i];
            vol[l][i] = rndint(GG);
        }
        long long c2 = evalcost();
        double temp = T0 * (1.0 - (double)it / iters) + 0.05;
        if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
        } else {
            if (swap_kind) {
                int t = perm[l][i];
                perm[l][i] = perm[l][i2];
                perm[l][i2] = t;
            } else {
                vol[l][i] = oldv;
            }
        }
    }
    return cur == 0 ? 1 : 0;
}

static int bestK = 0, bestGM = 1, bestGK = 1, bestR = 1;
static long long bestN = 0;
static int bestPerm[MAXDEG][MAXK], bestVol[MAXDEG][MAXK];

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long long minN = atoll(argv[5]);
    if (DEG < 1 || DEG > MAXDEG || DIA < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    DEADLINE = now_s() + budget;
    bestN = minN;
    static const int KCH[10] = {1, 1, 2, 2, 2, 3, 3, 4, 5, 6};

    while (now_s() < DEADLINE) {
        int K = KCH[rndint(10)];
        long long gmin = bestN / (2LL * K) + 1;
        long long spread = gmin / 16 + 2;
        long long G = gmin + rndint((int)spread);
        if (G < 1) G = 1;

        int cand[64], nc = 0;
        for (int x = 1; x <= 40 && x <= G; x++)
            if (G % x == 0) cand[nc++] = x;
        int k2 = cand[rndint(nc)];
        int m = (int)(G / k2);
        int r = pick_r(m, k2);

        long long N = 2LL * K * G;
        if (N > INT_MAX || N <= bestN) continue;
        set_group(m, k2, r);
        KL = K;
        ensure_cap((int)N);

        int ok = anneal(ITERS, 2.0, DEADLINE);
        if (ok < 0) break;
        if (ok == 1 && N > bestN) {
            bestN = N;
            bestK = K;
            bestGM = m;
            bestGK = k2;
            bestR = r;
            memcpy(bestPerm, perm, sizeof perm);
            memcpy(bestVol, vol, sizeof vol);
        }
    }

    if (bestK == 0) {
        printf("0 0\n");
        return 0;
    }
    KL = bestK;
    memcpy(perm, bestPerm, sizeof perm);
    memcpy(vol, bestVol, sizeof vol);
    set_group(bestGM, bestGK, bestR);
    int K = KL, d = DEG, G = GG;
    int N = 2 * K * G;
    long m = (long)d * K * G;
    printf("%d %ld\n", N, m);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) {
            int j = perm[l][i], s = vol[l][i];
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + j) * G + gmul(g, s));
            }
        }
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search from the best order.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
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

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C, seeded with the best known order as a lower bound.
    if d >= 3 and D >= 3 and time_limit > 12:
        budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                            timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
