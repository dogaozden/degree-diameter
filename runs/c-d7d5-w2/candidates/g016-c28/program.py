import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A (lift search): simulated annealing over voltages of a bi-Cayley lift
# over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Each dart e = l*K + i
# joins A_i to B_{dJ[e]} with voltage dS[e]. The cost is the total excess
# distance from the 2K representatives, zero iff the lift has diameter <= DIAM.
# Usage: prog d D K m k2 r seed slice_seconds. Prints "n m" + edges, or "0 0".
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
# Engine B (growth by edge-switch repair): a different, unstructured search.
# Input: a bipartite graph with every edge written as (A-vertex, B-vertex).
# Each step inserts a fresh pair (a, b) by rewiring random edges (x, y) into
# (x, b) plus a new edge (a, y), which keeps all old degrees and gives a and b
# degree DEG. Then simulated annealing with degree-preserving two-edge swaps
# minimises the number of vertex pairs at distance > DIAM (bitset BFS).
# Whenever the cost reaches zero the graph is saved and grown again.
# Usage: prog d D seed slice_seconds. Prints "n m" + edges, or "0 0".
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXPAIRS 600
#define STAG 1500
#define ITERS 2500

static int DEG, DIAM, N, NMAX, E, EMAX, W, STRIDE;
static int *eA, *eB, *bestA, *bestB, *deg, *adj;
static int bestN = 0, bestE = 0;
static unsigned char *M;
static uint64_t *R1, *R2;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static inline int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_nb(int v, int nw) {
    adj[(size_t)v * STRIDE + deg[v]++] = nw;
}

static void rm_nb(int v, int old) {
    int *av = adj + (size_t)v * STRIDE;
    for (int i = 0; i < deg[v]; i++) {
        if (av[i] == old) { av[i] = av[deg[v] - 1]; deg[v]--; return; }
    }
}

static void add_edge(int a, int b) {
    eA[E] = a; eB[E] = b; E++;
    add_nb(a, b); add_nb(b, a);
    M[(size_t)a * NMAX + b] = 1; M[(size_t)b * NMAX + a] = 1;
}

/* Move the B end of edge e from its current vertex to nb. Keeps A end. */
static void set_edge_b(int e, int nb) {
    int a = eA[e], ob = eB[e];
    int *aa = adj + (size_t)a * STRIDE;
    for (int i = 0; i < deg[a]; i++) {
        if (aa[i] == ob) { aa[i] = nb; break; }
    }
    rm_nb(ob, a);
    add_nb(nb, a);
    M[(size_t)a * NMAX + ob] = 0; M[(size_t)ob * NMAX + a] = 0;
    M[(size_t)a * NMAX + nb] = 1; M[(size_t)nb * NMAX + a] = 1;
    eB[e] = nb;
}

static void rebuild(void) {
    memset(deg, 0, sizeof(int) * (size_t)NMAX);
    memset(M, 0, (size_t)NMAX * NMAX);
    for (int e = 0; e < E; e++) {
        int a = eA[e], b = eB[e];
        add_nb(a, b); add_nb(b, a);
        M[(size_t)a * NMAX + b] = 1; M[(size_t)b * NMAX + a] = 1;
    }
}

static void save_restart(void) {
    bestN = N; bestE = E;
    memcpy(bestA, eA, sizeof(int) * (size_t)E);
    memcpy(bestB, eB, sizeof(int) * (size_t)E);
}

static void load_restart(void) {
    N = bestN; E = bestE;
    memcpy(eA, bestA, sizeof(int) * (size_t)E);
    memcpy(eB, bestB, sizeof(int) * (size_t)E);
    rebuild();
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static int eval_cost(void) {
    int Wn = (N + 63) / 64;
    uint64_t *R = R1, *T = R2;
    for (int v = 0; v < N; v++) {
        uint64_t *r = R + (size_t)v * W;
        for (int w = 0; w < Wn; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int rd = 0; rd < DIAM; rd++) {
        for (int v = 0; v < N; v++) {
            uint64_t *t = T + (size_t)v * W;
            const uint64_t *s = R + (size_t)v * W;
            for (int w = 0; w < Wn; w++) t[w] = s[w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *su = R + (size_t)adj[(size_t)v * STRIDE + i] * W;
                for (int w = 0; w < Wn; w++) t[w] |= su[w];
            }
        }
        uint64_t *tmp = R; R = T; T = tmp;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *r = R + (size_t)v * W;
        for (int w = 0; w < Wn; w++) c += popc64(r[w]);
        cost += N - c;
    }
    return (int)(cost / 2);
}

/* Swap the B ends of e1=(a1,b1) and e2=(a2,b2) into (a1,b2) and (a2,b1). */
static int try_swap(int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = eA[e1], b1 = eB[e1], a2 = eA[e2], b2 = eB[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (M[(size_t)a1 * NMAX + b2] || M[(size_t)a2 * NMAX + b1]) return 0;
    set_edge_b(e1, b2);
    set_edge_b(e2, b1);
    return 1;
}

static void undo_swap(int e1, int e2, int b1, int b2) {
    set_edge_b(e2, b2);
    set_edge_b(e1, b1);
}

/* Insert a new pair (a, b) with edge a-b and DEG-1 rewirings. Returns 1 on success. */
static int insert_pair(void) {
    int a = N, b = N + 1;
    N += 2;
    add_edge(a, b);
    for (int k = 1; k < DEG; k++) {
        int found = 0;
        for (int tr = 0; tr < 4000 && !found; tr++) {
            int e1 = rndint(E);
            int x = eA[e1], y = eB[e1];
            if (x == a || x == b || y == a || y == b) continue;
            if (M[(size_t)x * NMAX + b] || M[(size_t)a * NMAX + y]) continue;
            set_edge_b(e1, b);
            add_edge(a, y);
            found = 1;
        }
        if (!found) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    NMAX = n0 + 2 * MAXPAIRS;
    EMAX = m0 + DEG * MAXPAIRS + 4;
    STRIDE = DEG + 1;
    W = (NMAX + 63) / 64;

    eA = malloc(sizeof(int) * (size_t)EMAX);
    eB = malloc(sizeof(int) * (size_t)EMAX);
    bestA = malloc(sizeof(int) * (size_t)EMAX);
    bestB = malloc(sizeof(int) * (size_t)EMAX);
    deg = calloc((size_t)NMAX, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)NMAX * STRIDE);
    M = calloc((size_t)NMAX * NMAX, 1);
    R1 = calloc((size_t)NMAX * W, sizeof(uint64_t));
    R2 = calloc((size_t)NMAX * W, sizeof(uint64_t));
    int *dc = calloc((size_t)n0, sizeof(int));
    if (!eA || !eB || !bestA || !bestB || !deg || !adj || !M || !R1 || !R2 || !dc) {
        printf("0 0\n");
        return 0;
    }

    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) { bad = 1; break; }
        dc[u]++; dc[v]++;
        if (dc[u] > DEG || dc[v] > DEG) { bad = 1; break; }
        eA[i] = u; eB[i] = v;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    N = n0; E = m0;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    rebuild();
    int haveValid = (eval_cost() == 0);
    save_restart();

    clock_t t0 = clock();
    while (elapsed(t0) < slice) {
        load_restart();
        int cur = eval_cost();
        if (cur == 0) {
            if (N + 2 > NMAX || E + DEG > EMAX) break;
            if (!insert_pair()) continue;
            cur = eval_cost();
        }

        int found = 0;
        double T0 = 2.0;
        int bc = cur, since = 0;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 63) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / ITERS) + 0.02;
            int e1 = rndint(E), e2 = rndint(E);
            int b1 = eB[e1], b2 = eB[e2];
            if (!try_swap(e1, e2)) continue;
            int nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                undo_swap(e1, e2, b1, b2);
            }
            if (cur < bc) { bc = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
        if (found) {
            save_restart();
            haveValid = 1;
        }
    }

    if (!haveValid) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestE);
    for (int e = 0; e < bestE; e++) {
        printf("%d %d\n", bestA[e], bestB[e]);
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact construction and helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
            if math.gcd(1, m) == 1:
                return m, k2, 1
    return None


def _grow(d, D, graph, rng, slice_s):
    """Run the edge-switch growth engine on a graph; returns (n, edges) or None."""
    n, e = graph
    col = _two_colour(n, e)
    if col is None:
        return None
    oriented = [(u, v) if col[u] == 0 else (v, u) for u, v in e]
    out = lib.run_c(C_GROW, [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    stdin_graph=(n, oriented), timeout=slice_s + 10.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
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

    # Stage 1: voltage-lift search (first half of the budget).
    lift_deadline = start + 0.5 * budget
    step = 0.08
    while True:
        remaining = lift_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        want = best[0] * (1.0 + step)
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
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if consider(n, e):
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)

    # Stage 2: edge-switch growth from the best graph (remaining budget).
    remaining = deadline - time.monotonic() - 1.0
    if best[0] >= 4 and remaining >= 2.0:
        try:
            g = _grow(d, D, best, rng, remaining)
            if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
