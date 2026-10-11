import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (voltage lifts, carried over from the parent): simulated annealing
# over the voltages of a bi-Cayley lift over Z_m x|_r Z_k2.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
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

/* Excess-distance cost. Zero iff every representative reaches every vertex
   within DIAM steps (valid lift), plus a duplicate-dart penalty. */
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

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
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
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
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
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
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

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
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

        int runBest = cur;
        int since = 0;
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
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
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
# Engine 2 (new): Haar graphs over an arbitrary group of order G.
#
# Vertices: A_x = x and B_y = G + y. Edges A_x ~ B_(s*x) for s in S, |S| = DEG.
# Right multiplication is an automorphism, so the diameter is at most DIAM iff
# A_identity and B_identity both reach every vertex within DIAM steps.
# Cost = unreached vertices from those two sources; zero means valid.
# Moves replace one element of S; simulated annealing with restarts from the
# best subset (kick + anneal). The group is built inside C from a description:
#   kind 0: abelian product of cyclic factors  -> "0 nf f1 ... fnf"
#   kind 1: Z_m x|_r Z_k (r^k = 1 mod m)       -> "1 m k r"
#
# Usage: prog d D seed slice kind ...   Prints a valid graph or "0 0".
# ----------------------------------------------------------------------------

NEW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXF 16
#define GMAX 3000
#define STAG 30000
#define RLEN 150000

static int G, DEG, DIAM, NN;
static int KIND, NF, FAC[MAXF], SM, SK;
static int *POWR, *mt, *inv, *S, *iS, *inS, *stampv, *fr, *nx, *bestS;
static int stamp_c = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int fail_out(void) {
    printf("0 0\n");
    return 0;
}

/* Group multiplication on coded elements; identity is 0. */
static int gmul_raw(int x, int y) {
    if (KIND == 0) {
        long long res = 0, place = 1;
        for (int i = 0; i < NF; i++) {
            long long f = FAC[i];
            long long cx = ((long long)x / place) % f;
            long long cy = ((long long)y / place) % f;
            res += ((cx + cy) % f) * place;
            place *= f;
        }
        return (int)res;
    } else {
        int a = x / SK, b = x % SK, c = y / SK, dd = y % SK;
        long long t = ((long long)a + (long long)POWR[b] * c) % SM;
        return (int)(t * SK + (b + dd) % SK);
    }
}

/* BFS from src; returns how many nodes lie within DIAM steps. */
static int reach_count(int src) {
    if (++stamp_c >= 0x3fffffff) {
        memset(stampv, 0, sizeof(int) * (size_t)NN);
        stamp_c = 1;
    }
    int *cur = fr, *nxt = nx;
    int fn = 1, reached = 1;
    cur[0] = src;
    stampv[src] = stamp_c;
    for (int lv = 0; lv < DIAM && fn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < fn; q++) {
            int u = cur[q];
            if (u < G) {
                for (int j = 0; j < DEG; j++) {
                    int v = G + mt[S[j] * G + u];
                    if (stampv[v] != stamp_c) {
                        stampv[v] = stamp_c;
                        nxt[nn++] = v;
                    }
                }
            } else {
                int y = u - G;
                for (int j = 0; j < DEG; j++) {
                    int v = mt[iS[j] * G + y];
                    if (stampv[v] != stamp_c) {
                        stampv[v] = stamp_c;
                        nxt[nn++] = v;
                    }
                }
            }
        }
        reached += nn;
        int *tmp = cur; cur = nxt; nxt = tmp;
        fn = nn;
    }
    return reached;
}

static int cost_fn(void) {
    int r1 = reach_count(0);
    int r2 = reach_count(G);
    return (NN - r1) + (NN - r2);
}

static void setel(int j, int t) {
    inS[S[j]] = 0;
    inS[t] = 1;
    S[j] = t;
    iS[j] = inv[t];
}

static void random_subset(void) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    for (int j = 0; j < DEG; j++) {
        int t;
        do { t = rndint(G); } while (inS[t]);
        inS[t] = 1;
        S[j] = t;
        iS[j] = inv[t];
    }
}

int main(int argc, char **argv) {
    if (argc < 6) return fail_out();
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    KIND = atoi(argv[5]);

    if (KIND == 0) {
        if (argc < 7) return fail_out();
        NF = atoi(argv[6]);
        if (NF < 1 || NF > MAXF || argc < 7 + NF) return fail_out();
        G = 1;
        for (int i = 0; i < NF; i++) {
            FAC[i] = atoi(argv[7 + i]);
            if (FAC[i] < 1 || G > GMAX / FAC[i]) return fail_out();
            G *= FAC[i];
        }
    } else if (KIND == 1) {
        if (argc < 9) return fail_out();
        SM = atoi(argv[6]);
        SK = atoi(argv[7]);
        int r = atoi(argv[8]);
        if (SM < 1 || SK < 1 || SM > GMAX || SK > GMAX || SM * SK > GMAX) return fail_out();
        G = SM * SK;
        POWR = malloc(sizeof(int) * (size_t)SK);
        if (!POWR) return fail_out();
        int rr = ((r % SM) + SM) % SM;
        POWR[0] = 1 % SM;
        for (int b = 1; b < SK; b++) POWR[b] = (int)((long long)POWR[b - 1] * rr % SM);
        if ((((long long)POWR[SK - 1]) * rr) % SM != 1 % SM) return fail_out();
    } else {
        return fail_out();
    }
    if (DEG < 1 || DIAM < 1 || DEG >= G) return fail_out();

    NN = 2 * G;
    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    inv = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    iS = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    inS = calloc((size_t)G, sizeof(int));
    stampv = calloc((size_t)NN, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NN);
    nx = malloc(sizeof(int) * (size_t)NN);
    if (!mt || !inv || !S || !iS || !bestS || !inS || !stampv || !fr || !nx) return fail_out();

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[x * G + y] = gmul_raw(x, y);
    for (int y = 0; y < G; y++)
        if (mt[y] != y) return fail_out();
    for (int x = 0; x < G; x++) inv[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mt[x * G + y] == 0) inv[x] = y;
    for (int x = 0; x < G; x++)
        if (inv[x] < 0) return fail_out();

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int bestCost = 1 << 30;
    int haveBest = 0, found = 0;

    while (!found && elapsed(t0) < slice) {
        if (!haveBest || rnd01() < 0.4) {
            random_subset();
        } else {
            memset(inS, 0, sizeof(int) * (size_t)G);
            for (int j = 0; j < DEG; j++) {
                S[j] = bestS[j];
                inS[S[j]] = 1;
                iS[j] = inv[S[j]];
            }
            for (int k = 0; k < 3; k++) {
                int j = rndint(DEG), t;
                do { t = rndint(G); } while (inS[t]);
                setel(j, t);
            }
        }
        int cur = cost_fn();
        if (cur < bestCost) {
            bestCost = cur;
            memcpy(bestS, S, sizeof(int) * (size_t)DEG);
            haveBest = 1;
        }
        if (cur == 0) { found = 1; break; }

        const double T0 = 1.5;
        int runBest = cur, since = 0;
        for (int it = 0; it < RLEN; it++) {
            if ((it & 511) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RLEN) + 0.03;
            int j = rndint(DEG);
            int t = rndint(G);
            if (inS[t]) continue;
            int old = S[j];
            setel(j, t);
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                setel(j, old);
            }
            if (cur < bestCost) {
                bestCost = cur;
                memcpy(bestS, S, sizeof(int) * (size_t)DEG);
                haveBest = 1;
            }
            if (cur == 0) { found = 1; break; }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
        }
    }

    if (found) {
        printf("%d %d\n", NN, G * DEG);
        for (int x = 0; x < G; x++)
            for (int j = 0; j < DEG; j++)
                printf("%d %d\n", x, G + mt[S[j] * G + x]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""

HAAR_MAX_G = 1500


# ----------------------------------------------------------------------------
# Exact / safe constructions (carried over).
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


def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _extend_spare(n, edges, d, D, deadline):
    """Greedily add fresh vertex pairs while the graph stays valid. Returns (n, edges)."""
    if d < 2:
        return n, edges
    col = _two_colour(n, edges)
    if col is None:
        return n, edges
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A_sp = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B_sp = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A_sp or not B_sp:
            break
        grown = False
        for k in range(d - 1, 0, -1):
            if k > len(A_sp) or k > len(B_sp):
                continue
            a, b = n, n + 1
            cand_new = [(a, b)] + [(a, x) for x in B_sp[:k]] + [(b, y) for y in A_sp[:k]]
            cand = edges + cand_new
            if lib.is_valid(n + 2, cand, d, D):
                edges = cand
                n += 2
                col += [0, 1]
                deg += [0, 0]
                deg[a] = k + 1
                deg[b] = k + 1
                for x in B_sp[:k]:
                    deg[x] += 1
                for y in A_sp[:k]:
                    deg[y] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling for both engines.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m0 = max(2, -(-target // k2))
        for m in range(m0, m0 + 40):
            if k2 == 1:
                return m, 1, 1
            nontrivial = [c for c in range(2, m)
                          if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if nontrivial:
                return m, k2, rng.choice(nontrivial)
            if pow(1, k2, m) == 1 % m and math.gcd(1, m) == 1:
                return m, k2, 1
    return None


def _prime_factors(n):
    """Prime factors of n with multiplicity (empty for n = 1)."""
    out, p = [], 2
    while p * p <= n:
        while n % p == 0:
            out.append(p)
            n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


def _haar_group_args(G, rng):
    """Argument list describing a group of order exactly G for NEW_SOURCE."""
    primes = _prime_factors(G)
    if len(primes) >= 2 and rng.random() < 0.5:
        ks = [k for k in range(2, G) if G % k == 0]
        rng.shuffle(ks)
        for k in ks:
            m = G // k
            if m < 3:
                continue
            twists = [r for r in range(2, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if twists:
                return ["1", str(m), str(k), str(rng.choice(twists))]
    if len(primes) >= 2 and rng.random() < 0.6:
        rng.shuffle(primes)
        s = rng.randint(2, min(4, len(primes)))
        buckets = [1] * s
        for i, p in enumerate(primes):
            j = i if i < s else rng.randrange(s)
            buckets[j] *= p
        return ["0", str(s)] + [str(b) for b in buckets]
    return ["0", "1", str(G)]


# ----------------------------------------------------------------------------
# Driver: portfolio of the Haar engine (main, new) and the lift engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    search_deadline = start + 0.92 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid. Returns True when the best improved."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

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

    engines = {"haar": True, "lift": True}
    steps = {"haar": 0.08, "lift": 0.08}

    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        enabled = [e for e in ("haar", "lift") if engines[e]]
        if not enabled:
            break
        if len(enabled) == 1 or rng.random() < 0.7:
            eng = "haar" if "haar" in enabled else "lift"
        else:
            eng = "lift"
        slice_s = min(remaining, 8.0)

        if eng == "haar":
            G = max(d + 1, math.ceil(best[0] * (1.0 + steps["haar"]) / 2))
            if G > HAAR_MAX_G:
                engines["haar"] = False
                continue
            gargs = _haar_group_args(G, rng)
            args = [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"] + gargs
            try:
                out = lib.run_c(NEW_SOURCE, args, timeout=slice_s + 10.0)
            except RuntimeError:
                engines["haar"] = False
                continue
            try:
                n, e = lib.parse_graph_text(out)
                ok = consider(n, e)
            except ValueError:
                ok = False
            if ok:
                steps["haar"] = min(0.4, steps["haar"] * 1.25)
            else:
                steps["haar"] = max(0.005, steps["haar"] * 0.85)
        else:
            k = rng.choice([1, 1, 2, 2, 3])
            want = best[0] * (1.0 + steps["lift"])
            target = max(2, math.ceil(want / (2 * k)))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            try:
                out = lib.run_c(
                    C_LIFT,
                    [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                engines["lift"] = False
                continue
            try:
                n, e = lib.parse_graph_text(out)
                ok = consider(n, e)
            except ValueError:
                ok = False
            if ok:
                steps["lift"] = min(0.4, steps["lift"] * 1.25)
            else:
                steps["lift"] = max(0.005, steps["lift"] * 0.8)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension on the best graph, with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
