import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: Haar graphs of metacyclic groups.
#
# For a group Gamma of order G (here Z_M semidirect Z_K with r^K = 1 mod M)
# and a connection set S of DEG distinct elements, the bipartite graph has
# A-vertices x and B-vertices y (0..G-1 each), with A_x adjacent to B_{x*s}
# for every s in S. Each vertex has degree DEG.
#
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS
# of depth D from A_identity and from B_identity reaches every vertex. The C
# engine searches over S by simulated annealing, one random group per attempt,
# and keeps the largest group order that succeeds.
#
# This replaces the earlier multi-block voltage lift with a single-orbit search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1600
#define ITERS 60000
#define MAXDIV 64

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM;
static int G, GM, GK, GR;
static int *mulT = NULL;
static int *Rp = NULL;
static int *S = NULL, *Sb = NULL, *Sbest = NULL;
static char *inS = NULL;
static int *adj = NULL, *cnt = NULL, *stamp = NULL, *fr = NULL, *nx = NULL;
static int curstamp = 0;
static int best_G = 0, bestM = 0, bestK = 0, bestR = 0;
static int have_best = 0;

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,e) = (a + r^b c, b + e), element index a*GK + b. */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK;
    int c = y / GK, e = y % GK;
    int ra = (int)(((long long)a + (long long)Rp[b] * c) % GM);
    int rb = (b + e) % GK;
    return ra * GK + rb;
}

static void build_group(int M, int K, int R) {
    GM = M; GK = K; GR = R; G = M * K;
    Rp = malloc(sizeof(int) * (size_t)K);
    Rp[0] = 1 % M;
    for (int b = 1; b < K; b++) Rp[b] = (int)((long long)Rp[b - 1] * R % M);
    mulT = malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[(size_t)x * G + y] = gmul(x, y);
}

static void free_group(void) {
    free(mulT);
    free(Rp);
    mulT = NULL;
    Rp = NULL;
}

/* A_x (index x) joins B_{x*s} (index G + x*s) for every s in S. */
static void build_adj(void) {
    int N = 2 * G;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int x = 0; x < G; x++) {
        const int *row = mulT + (size_t)x * G;
        for (int i = 0; i < DEG; i++) {
            int y = row[S[i]];
            int a = x, b = G + y;
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
}

static int reach(int src) {
    int N = 2 * G;
    if (curstamp >= 1000000000) {
        memset(stamp, 0, sizeof(int) * (size_t)N);
        curstamp = 0;
    }
    curstamp++;
    int *f = fr, *h = nx;
    int fsz = 1, count = 1;
    f[0] = src;
    stamp[src] = curstamp;
    for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
        int nsz = 0;
        for (int q = 0; q < fsz; q++) {
            const int *au = adj + (size_t)f[q] * DEG;
            for (int e = 0; e < DEG; e++) {
                int v = au[e];
                if (stamp[v] != curstamp) {
                    stamp[v] = curstamp;
                    h[nsz++] = v;
                }
            }
        }
        count += nsz;
        int *tmp = f; f = h; h = tmp;
        fsz = nsz;
    }
    return count;
}

/* Number of (source, vertex) pairs left uncovered, over the two orbit representatives. */
static long long eval_cost(void) {
    int N = 2 * G;
    build_adj();
    int a = reach(0);
    int b = reach(G);
    return (long long)(N - a) + (long long)(N - b);
}

static void random_S(void) {
    memset(inS, 0, (size_t)G);
    for (int i = 0; i < DEG; i++) {
        int v;
        do { v = rnd_int(G); } while (inS[v]);
        inS[v] = 1;
        S[i] = v;
    }
}

/* Simulated annealing over S. Leaves the best state found in Sb and returns its cost. */
static long long anneal(int iters) {
    random_S();
    long long cur = eval_cost();
    long long bestc = cur;
    memcpy(Sb, S, sizeof(int) * (size_t)DEG);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 255) == 0 && elapsed() > DEADLINE) break;
        double temp = 1.5 * (1.0 - (double)it / iters) + 0.03;
        int i = rnd_int(DEG);
        int old = S[i];
        int nw = rnd_int(G);
        if (inS[nw]) continue;
        inS[old] = 0;
        inS[nw] = 1;
        S[i] = nw;
        long long c2 = eval_cost();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / temp)) {
            cur = c2;
            if (cur < bestc) {
                bestc = cur;
                memcpy(Sb, S, sizeof(int) * (size_t)DEG);
            }
        } else {
            inS[nw] = 0;
            inS[old] = 1;
            S[i] = old;
        }
    }
    return bestc;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    best_G = start_n / 2;
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    adj = malloc(sizeof(int) * (size_t)2 * MAXG * DEG);
    cnt = malloc(sizeof(int) * (size_t)2 * MAXG);
    stamp = calloc((size_t)2 * MAXG, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)2 * MAXG);
    nx = malloc(sizeof(int) * (size_t)2 * MAXG);
    inS = malloc((size_t)MAXG);
    S = malloc(sizeof(int) * (size_t)DEG);
    Sb = malloc(sizeof(int) * (size_t)DEG);
    Sbest = malloc(sizeof(int) * (size_t)DEG);

    while (elapsed() < DEADLINE) {
        int spread = 2 + best_G / 60;
        int g = best_G + 1 + rnd_int(spread);
        if (g > MAXG) {
            g = best_G + 1;
            if (g > MAXG) break;
        }
        if (g < DEG) g = DEG;

        int divs[MAXDIV], nd = 0;
        for (int k = 1; k <= g && nd < MAXDIV; k++)
            if (g % k == 0) divs[nd++] = k;

        int M = g, K = 1, R = 1 % g;
        int ok = 0;
        for (int tr = 0; tr < 40 && !ok; tr++) {
            int kk = divs[rnd_int(nd)];
            int mm = g / kk;
            if (kk == 1) {
                M = mm; K = 1; R = 1 % mm; ok = 1;
                break;
            }
            for (int t2 = 0; t2 < 300 && !ok; t2++) {
                int r = (mm == 1) ? 0 : rnd_int(mm);
                if (gcd_i(r, mm) == 1 && powmod(r, kk, mm) == 1 % mm) {
                    M = mm; K = kk; R = r; ok = 1;
                }
            }
        }

        build_group(M, K, R);
        if (G >= DEG) {
            long long c = anneal(ITERS);
            if (c == 0) {
                best_G = G;
                bestM = M;
                bestK = K;
                bestR = R;
                memcpy(Sbest, Sb, sizeof(int) * (size_t)DEG);
                have_best = 1;
            }
        }
        free_group();
    }

    if (have_best) {
        build_group(bestM, bestK, bestR);
        int n = 2 * G;
        long long m = (long long)G * DEG;
        printf("%d %lld\n", n, m);
        for (int x = 0; x < G; x++) {
            const int *row = mulT + (size_t)x * G;
            for (int i = 0; i < DEG; i++)
                printf("%d %d\n", x, G + row[Sbest[i]]);
        }
        free_group();
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baselines in Python, then the C Haar-group annealer.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Give the C search most of the budget; leave room for the compile step,
    # parsing and validation.
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
