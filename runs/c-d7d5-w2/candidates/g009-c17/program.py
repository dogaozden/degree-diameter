import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (LIFT_SOURCE): simulated annealing over the voltages of a bi-Cayley
# lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Used as the
# baseline generator. Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
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
# Engine 2 (GROW_SOURCE): a different search. Works on d-regular bipartite
# graphs with side S (A = 0..S-1, B = S..2S-1). It starts from a d-regular
# start graph (stdin, side s0 <= S, A-first labels) grown to side S by inserting
# vertex pairs with degree-preserving edge insertions, or from a Haar graph of
# side S. It then anneals with degree-preserving 2-switches. Cost = number of
# ordered vertex pairs at distance > D, computed with bitset ball expansion.
# Usage: prog d D S seed slice_seconds   (optional start graph on stdin)
# Prints a valid zero-cost graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int d, D, S, V, W, NE;
static int *ea, *eb, *adj, *cnt, *bea, *beb;
static uint64_t *cu, *nx;
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

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_adj(int a, int b) {
    const int *p = adj + (size_t)a * d;
    for (int k = 0; k < d; k++) if (p[k] == b) return 1;
    return 0;
}

static void repl(int x, int from, int to) {
    int *p = adj + (size_t)x * d;
    for (int k = 0; k < d; k++) if (p[k] == from) { p[k] = to; return; }
}

/* Swap the B endpoints of edges e1 and e2. Involutive: applying it twice restores the state. */
static void apply_swap(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    eb[e1] = b2;
    eb[e2] = b1;
    repl(a1, b1, b2);
    repl(a2, b2, b1);
    repl(b1, a1, a2);
    repl(b2, a2, a1);
}

static void add_edges(int upto) {
    for (int e = 0; e < upto; e++) {
        int a = ea[e], b = eb[e];
        adj[(size_t)a * d + cnt[a]++] = b;
        adj[(size_t)b * d + cnt[b]++] = a;
    }
}

static void rebuild_all(void) {
    memset(cnt, 0, sizeof(int) * (size_t)V);
    add_edges(NE);
}

/* Add the new pair (a = cs, b = S + cs) with d edges, keeping all degrees at d. */
static void grow_one(int cs) {
    int a = cs, b = S + cs;
    int E = cs * d;
    int chosen[64];
    int nch = 0;
    while (nch < d - 1) {
        int e = rndint(E);
        int ok = 1;
        for (int i = 0; i < nch; i++) {
            if (chosen[i] == e || ea[chosen[i]] == ea[e] || eb[chosen[i]] == eb[e]) { ok = 0; break; }
        }
        if (ok) chosen[nch++] = e;
    }
    for (int i = 0; i < d - 1; i++) {
        int e = chosen[i];
        int x = ea[e], y = eb[e];
        /* Remove (x,y); add (a,y) in slot e, (x,b) in a new slot. */
        repl(x, y, b);
        repl(y, x, a);
        adj[(size_t)a * d + cnt[a]++] = y;
        adj[(size_t)b * d + cnt[b]++] = x;
        ea[e] = a; eb[e] = y;
        ea[E + i] = x; eb[E + i] = b;
    }
    adj[(size_t)a * d + cnt[a]++] = b;
    adj[(size_t)b * d + cnt[b]++] = a;
    ea[E + d - 1] = a; eb[E + d - 1] = b;
}

static long cost_fn(void) {
    for (int v = 0; v < V; v++) {
        uint64_t *row = cu + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < V; v++) {
            uint64_t *o = nx + (size_t)v * W;
            memcpy(o, cu + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *p = adj + (size_t)v * d;
            for (int k = 0; k < d; k++) {
                const uint64_t *s = cu + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cu; cu = nx; nx = t;
    }
    long total = 0;
    for (int v = 0; v < V; v++) {
        const uint64_t *row = cu + (size_t)v * W;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += popc(row[w]);
        total += V - pc;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D S seed slice\n");
        return 1;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    S = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (d < 2 || d > 64 || D < 1 || S < d) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    V = 2 * S;
    W = (V + 63) / 64;
    NE = S * d;
    ea = malloc(sizeof(int) * (size_t)NE);
    eb = malloc(sizeof(int) * (size_t)NE);
    bea = malloc(sizeof(int) * (size_t)NE);
    beb = malloc(sizeof(int) * (size_t)NE);
    adj = malloc(sizeof(int) * (size_t)V * d);
    cnt = malloc(sizeof(int) * (size_t)V);
    cu = malloc(sizeof(uint64_t) * (size_t)V * W);
    nx = malloc(sizeof(uint64_t) * (size_t)V * W);
    if (!ea || !eb || !bea || !beb || !adj || !cnt || !cu || !nx) { printf("0 0\n"); return 0; }

    /* Optional start graph: must be d-regular bipartite, A-first labels, side s0 <= S. */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    int usable = 0, s0 = 0;
    int *su = NULL, *sv = NULL;
    if (n0 > 0 && m0 > 0 && n0 % 2 == 0) {
        s0 = n0 / 2;
        if (s0 <= S && s0 >= d && m0 == s0 * d) {
            su = malloc(sizeof(int) * (size_t)m0);
            sv = malloc(sizeof(int) * (size_t)m0);
            int *dg = calloc((size_t)n0, sizeof(int));
            int ok = (su && sv && dg);
            for (int i = 0; ok && i < m0; i++) {
                int u, v;
                if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
                if (u < 0 || v < 0 || u >= n0 || v >= n0) { ok = 0; break; }
                if (u < s0 && v >= s0) { su[i] = u; sv[i] = v; }
                else if (v < s0 && u >= s0) { su[i] = v; sv[i] = u; }
                else { ok = 0; break; }
                dg[u]++;
                dg[v]++;
            }
            if (ok) for (int v = 0; v < n0; v++) if (dg[v] != d) { ok = 0; break; }
            if (ok) {
                for (int i = 0; i < m0 && ok; i++)
                    for (int j = i + 1; j < m0; j++)
                        if (su[i] == su[j] && sv[i] == sv[j]) { ok = 0; break; }
            }
            usable = ok;
            free(dg);
        }
    }

    int cs;
    memset(cnt, 0, sizeof(int) * (size_t)V);
    if (usable) {
        for (int i = 0; i < m0; i++) {
            ea[i] = su[i];
            eb[i] = S + (sv[i] - s0);
        }
        add_edges(m0);
        cs = s0;
        while (cs < S) { grow_one(cs); cs++; }
    } else {
        for (int i = 0; i < S; i++)
            for (int t = 0; t < d; t++) {
                ea[i * d + t] = i;
                eb[i * d + t] = S + (i + t) % S;
            }
        rebuild_all();
    }
    free(su);
    free(sv);

    clock_t t0 = clock();
    long cc = cost_fn();
    long bestC = cc;
    memcpy(bea, ea, sizeof(int) * (size_t)NE);
    memcpy(beb, eb, sizeof(int) * (size_t)NE);
    int found = (cc == 0);
    const int RL = 3000;
    int first = 1;

    while (!found && elapsed(t0) < slice) {
        if (!first) {
            /* Restart from the best state with a random kick. */
            memcpy(ea, bea, sizeof(int) * (size_t)NE);
            memcpy(eb, beb, sizeof(int) * (size_t)NE);
            rebuild_all();
            int kick = 2 + NE / 60;
            int tries = kick * 8;
            while (kick > 0 && tries-- > 0) {
                int e1 = rndint(NE), e2 = rndint(NE);
                if (e1 == e2) continue;
                int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
                if (a1 == a2 || b1 == b2 || has_adj(a1, b2) || has_adj(a2, b1)) continue;
                apply_swap(e1, e2);
                kick--;
            }
            cc = cost_fn();
            if (cc == 0) { found = 1; break; }
        }
        first = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 15) == 0 && elapsed(t0) >= slice) break;
            double T = 1.2 * (1.0 - (double)it / RL) + 0.03;
            int e1 = rndint(NE), e2 = rndint(NE);
            if (e1 == e2) continue;
            int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
            if (a1 == a2 || b1 == b2 || has_adj(a1, b2) || has_adj(a2, b1)) continue;
            apply_swap(e1, e2);
            long nc = cost_fn();
            if (nc <= cc || rnd01() < exp(-(double)(nc - cc) / T)) {
                cc = nc;
            } else {
                apply_swap(e1, e2);
            }
            if (cc < bestC) {
                bestC = cc;
                memcpy(bea, ea, sizeof(int) * (size_t)NE);
                memcpy(beb, eb, sizeof(int) * (size_t)NE);
            }
            if (cc == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", V, NE);
        for (int e = 0; e < NE; e++) printf("%d %d\n", ea[e], eb[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and helpers.
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


def _is_regular_bip(n, edges, d):
    """True if every vertex has degree exactly d and n is even (A-first labels are checked in C)."""
    if n < 2 or n % 2:
        return False
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


# ----------------------------------------------------------------------------
# Driver. Phase 1: lift annealing gives a strong regular baseline.
# Phase 2: grow that baseline one side at a time with the bitset annealer.
# Every accepted graph passes lib.is_valid, and the fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    try:
        # Phase 1: lift baseline.
        lift_deadline = t0 + 0.3 * budget
        while True:
            remaining = lift_deadline - time.monotonic()
            if remaining < 1.0:
                break
            slice_s = min(remaining, 12.0)
            k = rng.choice([1, 1, 2, 2, 3])
            base = best[0] // (2 * k)
            target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            try:
                out = lib.run_c(
                    LIFT_SOURCE,
                    [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                break
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

        # Phase 2: grow the best regular graph one side at a time.
        fails = 0
        while fails < 4:
            remaining = deadline - time.monotonic() - 1.0
            if remaining < 2.0:
                break
            slice_s = min(remaining, 15.0)
            S = best[0] // 2 + 1
            stdin_g = best if _is_regular_bip(best[0], best[1], d) else None
            try:
                out = lib.run_c(
                    GROW_SOURCE,
                    [d, D, S, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    stdin_graph=stdin_g,
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                break
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                fails += 1
                continue
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                fails = 0
            else:
                fails += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
