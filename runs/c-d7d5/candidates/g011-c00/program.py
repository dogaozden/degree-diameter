import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine 1 (lift search, from the parent): simulated annealing over the voltages
# of a bi-Cayley lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
# Usage: prog d D K m k2 r seed slice_seconds. Prints a valid graph or "0 0".
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
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
# Engine 2 (new, bold): edge-level annealing on a general bipartite graph with
# max degree DEG. Vertices 0..NA-1 are side A, NA..N-1 side B. Input is a valid
# graph with some isolated new vertices. Moves: add an edge between deficient
# vertices, shift one endpoint of an edge onto a deficient vertex, or switch two
# edges (degree preserving). Cost = ordered pairs at distance > DIAM, computed
# with bitset BFS. Prints a valid graph of order N if cost reaches 0, else "0 0".
# Usage: prog DEG DIAM NA seed slice_seconds   (graph on stdin: "n m" + edges)
# ----------------------------------------------------------------------------

GROW_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int N, NA, DEG, DIAM, W;
static int *deg, *nbr, *defA, *defB;
static unsigned char *M;
static uint64_t *cur, *nxt;
static uint64_t rs = 88172645463325252ULL;
static double TEMP = 1.0;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void addE(int a, int b) {
    nbr[(size_t)a * DEG + deg[a]++] = b;
    nbr[(size_t)b * DEG + deg[b]++] = a;
    M[(size_t)a * N + b] = 1;
    M[(size_t)b * N + a] = 1;
}

static void delE(int a, int b) {
    int *la = nbr + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++) if (la[k] == b) { la[k] = la[--deg[a]]; break; }
    int *lb = nbr + (size_t)b * DEG;
    for (int k = 0; k < deg[b]; k++) if (lb[k] == a) { lb[k] = lb[--deg[b]]; break; }
    M[(size_t)a * N + b] = 0;
    M[(size_t)b * N + a] = 0;
}

static long cost_fn(void) {
    for (int v = 0; v < N; v++) {
        uint64_t *c = cur + (size_t)v * W;
        memset(c, 0, sizeof(uint64_t) * (size_t)W);
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *l = nbr + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur + (size_t)l[k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long good = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) good += popc(c[w]);
    }
    return (long)N * N - good;
}

static int accept(long delta) {
    if (delta <= 0) return 1;
    return rnd01() < exp(-(double)delta / TEMP);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int nA = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (DEG < 1 || DEG > 64 || DIAM < 1 || n < 2 || n > 3000 || nA < 1 || nA >= n || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    NA = nA;
    W = (N + 63) / 64;
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEF12345ULL;
    if (rs == 0) rs = 1;

    deg = calloc(N, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)N * DEG);
    M = calloc((size_t)N * N, 1);
    cur = calloc((size_t)N * W, sizeof(uint64_t));
    nxt = calloc((size_t)N * W, sizeof(uint64_t));
    defA = malloc(sizeof(int) * N);
    defB = malloc(sizeof(int) * N);
    if (!deg || !nbr || !M || !cur || !nxt || !defA || !defB) { printf("0 0\n"); return 0; }

    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u > v) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < NA && v >= NA && v < N)) { ok = 0; break; }
        if (deg[u] >= DEG || deg[v] >= DEG || M[(size_t)u * N + v]) { ok = 0; break; }
        addE(u, v);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    long curc = cost_fn();
    int found = (curc == 0);
    long it = 0;
    double frac = 0.0;

    while (!found) {
        if ((it & 7) == 0) {
            double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
            if (el >= slice) break;
            frac = el / slice;
            TEMP = 8.0 * (1.0 - frac) + 0.5;
        }
        it++;

        int nAd = 0, nBd = 0;
        for (int v = 0; v < NA; v++) if (deg[v] < DEG) defA[nAd++] = v;
        for (int v = NA; v < N; v++) if (deg[v] < DEG) defB[nBd++] = v;

        double r = rnd01();
        int type;
        if (r < 0.3 && nAd > 0 && nBd > 0) type = 0;
        else if (r < 0.5 && nBd > 0) type = 1;
        else if (r < 0.65 && nAd > 0) type = 2;
        else type = 3;

        if (type == 0) {
            int a = -1, b = -1;
            for (int t = 0; t < 12; t++) {
                int x = defA[rndint(nAd)], y = defB[rndint(nBd)];
                if (!M[(size_t)x * N + y]) { a = x; b = y; break; }
            }
            if (a < 0) continue;
            addE(a, b);
            long nc = cost_fn();
            if (accept(nc - curc)) {
                curc = nc;
            } else {
                delE(a, b);
            }
        } else if (type == 1) {
            int y = defB[rndint(nBd)];
            int x = -1, z = -1;
            for (int t = 0; t < 30; t++) {
                int xx = rndint(NA);
                if (deg[xx] > 0 && !M[(size_t)xx * N + y]) {
                    x = xx;
                    z = nbr[(size_t)xx * DEG + rndint(deg[xx])];
                    break;
                }
            }
            if (x < 0) continue;
            delE(x, z);
            addE(x, y);
            long nc = cost_fn();
            if (accept(nc - curc)) {
                curc = nc;
            } else {
                delE(x, y);
                addE(x, z);
            }
        } else if (type == 2) {
            int x = defA[rndint(nAd)];
            int z = -1, w = -1;
            for (int t = 0; t < 30; t++) {
                int zz = NA + rndint(N - NA);
                if (deg[zz] > 0 && !M[(size_t)x * N + zz]) {
                    z = zz;
                    w = nbr[(size_t)zz * DEG + rndint(deg[zz])];
                    break;
                }
            }
            if (z < 0) continue;
            delE(w, z);
            addE(x, z);
            long nc = cost_fn();
            if (accept(nc - curc)) {
                curc = nc;
            } else {
                delE(x, z);
                addE(w, z);
            }
        } else {
            int a1 = -1, b1 = -1, a2 = -1, b2 = -1;
            for (int t = 0; t < 30; t++) {
                int x1 = rndint(NA);
                if (deg[x1] == 0) continue;
                int y1 = nbr[(size_t)x1 * DEG + rndint(deg[x1])];
                int x2 = rndint(NA);
                if (deg[x2] == 0 || x2 == x1) continue;
                int y2 = nbr[(size_t)x2 * DEG + rndint(deg[x2])];
                if (y1 == y2) continue;
                if (M[(size_t)x1 * N + y2] || M[(size_t)x2 * N + y1]) continue;
                a1 = x1; b1 = y1; a2 = x2; b2 = y2;
                break;
            }
            if (a1 < 0) continue;
            delE(a1, b1);
            delE(a2, b2);
            addE(a1, b2);
            addE(a2, b1);
            long nc = cost_fn();
            if (accept(nc - curc)) {
                curc = nc;
            } else {
                delE(a1, b2);
                delE(a2, b1);
                addE(a1, b1);
                addE(a2, b2);
            }
        }
        if (curc == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    long mc = 0;
    for (int v = 0; v < N; v++) mc += deg[v];
    mc /= 2;
    printf("%d %ld\n", N, mc);
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < deg[v]; k++) {
            int u = nbr[(size_t)v * DEG + k];
            if (u > v) printf("%d %d\n", v, u);
        }
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


def _sides(n, edges):
    """Relabel a bipartite graph so side A is 0..NA-1 and side B is NA..n-1. Return (NA, NB, edges) or None."""
    col = _two_colour(n, edges)
    if col is None:
        return None
    A = [v for v in range(n) if col[v] == 0]
    B = [v for v in range(n) if col[v] == 1]
    lab = {}
    for i, v in enumerate(A):
        lab[v] = i
    for j, v in enumerate(B):
        lab[v] = len(A) + j
    E = []
    for u, v in edges:
        x, y = lab[u], lab[v]
        if x > y:
            x, y = y, x
        E.append((x, y))
    return len(A), len(B), E


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


# ----------------------------------------------------------------------------
# Stages.
# ----------------------------------------------------------------------------

def _lift_stage(d, D, rng, deadline, best):
    """Stage A: bi-Cayley lift search (proven baseline). Returns the best valid graph found."""
    failures = 0
    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 12.0)
        k = rng.choice([1, 1, 2, 2, 3])
        base = best[0] // (2 * k)
        target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
        grp = _sample_group(target, rng)
        if grp is None:
            failures += 1
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                LIFT_C_SOURCE,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            failures += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def _grow_stage(d, D, best, rng, deadline):
    """Stage B (new): add one A/B vertex pair at a time and anneal edges to restore diameter D."""
    fails = 0
    while fails < 6:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        rel = _sides(best[0], best[1])
        if rel is None:
            break
        NA, NB, E = rel
        # New A vertex is NA (isolated); old B vertices shift up by one; new B is last.
        start = (NA + NB + 2, [(a, b + 1) for a, b in E])
        slice_s = min(remaining - 1.0, 10.0)
        if slice_s < 1.0:
            break
        try:
            out = lib.run_c(
                GROW_C_SOURCE,
                [d, D, NA + 1, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=start,
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
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]

    # Exact construction: projective plane incidence graph, diameter 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Stage A gets most of the budget; stage B grows the best graph.
    lift_deadline = start + 0.65 * budget
    best = _lift_stage(d, D, rng, lift_deadline, best)
    best = _grow_stage(d, D, best, rng, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
