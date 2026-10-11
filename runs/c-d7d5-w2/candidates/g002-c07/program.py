import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: breakout local search over voltages of bi-Cayley lifts.
#
# Group: Z_m x|_r Z_k2, element (a, b) coded as a*k2 + b (needs r^k2 = 1 mod m).
# Base: K vertices per side, DEG layers, each layer a permutation of 0..K-1.
# Dart e = l*K + i joins A_i to B_{dJ[e]} with voltage dS[e]: A_{i,g} ~ B_{j,g*s}.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly.
#
# Search: weighted-violation local search (breakout). Each unreached (rep, vertex)
# pair has a weight. When the weighted cost stagnates, the weights of currently
# violated pairs grow, which pushes the search out of local minima. Moves change
# one voltage, or swap two targets inside one layer (degrees stay fixed).
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK2 60
#define TEMP 0.4
#define STAG 1500
#define RLEN 120000

static const long long PEN = 1000000000LL;

static int DEG, DIAM, K, MM, K2, G, N, NE, NR;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ, *vioIdx, *ptmp;
static long long *W;
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

/* Returns weighted cost; sets *violOut to the number of unreached pairs
   (their indices are stored in vioIdx) and *dupOut to duplicate darts. */
static long long cost_fn(int *violOut, int *dupOut) {
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

    long long total = 0;
    int nv = 0;
    for (int ri = 0; ri < NR; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1;
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
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        for (int v = 0; v < N; v++) {
            if (vis[v] != stamp) {
                size_t idx = (size_t)ri * N + v;
                total += W[idx];
                vioIdx[nv++] = (int)idx;
            }
        }
    }
    *violOut = nv;
    *dupOut = dup;
    return total + PEN * (long long)dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

static void random_layers(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) ptmp[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = ptmp[i]; ptmp[i] = ptmp[j]; ptmp[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = ptmp[i];
        }
    }
    for (int e = 0; e < NE; e++) {
        dS[e] = rndint(G);
        set_perm(e);
    }
}

static void kick_from_best(void) {
    memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
    memcpy(dS, bestS, sizeof(int) * (size_t)NE);
    int kick = NE / 6 + 1;
    for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
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

    if (DEG < 1 || DIAM < 1 || K < 1 || K > 4 || MM < 1 || K2 < 1 || K2 > MAXK2) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NR = 2 * K;
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
    vioIdx = malloc(sizeof(int) * (size_t)NR * N);
    W = malloc(sizeof(long long) * (size_t)NR * N);
    ptmp = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx
        || !vis || !vioIdx || !W || !ptmp) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int haveBest = 0;
    int bestViol = 1 << 30;

    while (!found && elapsed(t0) < slice) {
        if (!haveBest || rnd01() < 0.35) {
            random_layers();
            for (size_t i = 0; i < (size_t)NR * N; i++) W[i] = 1;
        } else {
            kick_from_best();
        }
        int curViol = 0, curDup = 0;
        long long cur = cost_fn(&curViol, &curDup);
        if (curDup == 0 && curViol < bestViol) {
            bestViol = curViol; save_best(); haveBest = 1;
        }
        if (curDup == 0 && curViol == 0) { found = 1; break; }

        long long runBest = cur;
        int since = 0;
        for (int it = 0; it < RLEN; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            int nv = 0, nd = 0;
            long long nc;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                nc = cost_fn(&nv, &nd);
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / TEMP)) {
                    cur = nc; curViol = nv; curDup = nd;
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
                nc = cost_fn(&nv, &nd);
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / TEMP)) {
                    cur = nc; curViol = nv; curDup = nd;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (curDup == 0 && curViol < bestViol) {
                bestViol = curViol; save_best(); haveBest = 1;
            }
            if (curDup == 0 && curViol == 0) { found = 1; break; }
            if (cur < runBest) {
                runBest = cur; since = 0;
            } else if (++since > STAG) {
                /* Breakout: raise weights of pairs violated by the current state. */
                cur = cost_fn(&curViol, &curDup);
                for (int k = 0; k < curViol; k++) W[vioIdx[k]] += 1;
                cur = cost_fn(&curViol, &curDup);
                runBest = cur;
                since = 0;
            }
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
# Greedy spare-degree extension (no-op for regular lifts).
# ----------------------------------------------------------------------------

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
# Group choice: metacyclic groups Z_m x|_r Z_k2 of an exact given order.
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng):
    """Shuffled list of (m, k2, r) with m * k2 == G, k2 <= 60, and r a valid action."""
    out = []
    for k2 in range(1, min(G, 60) + 1):
        if G % k2:
            continue
        m = G // k2
        if m == 1:
            out.append((1, k2, 1))
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            rs = [1]
        for r in rng.sample(rs, min(3, len(rs))):
            out.append((m, k2, r))
    rng.shuffle(out)
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.9 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d (optimal for D = 2).
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

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

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: breakout local search over bi-Cayley lifts, aiming above the
    # current best order each time.
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining, 7.0)
        K = rng.choice([1, 1, 2, 2, 3])
        G_min = best[0] // (2 * K) + 1
        G = G_min + rng.randrange(0, G_min // 30 + 2)
        groups = _groups_of_order(G, rng)
        if not groups:
            continue
        m, k2, r = groups[0]
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, K, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 15.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Spare-degree extension with the remaining time.
    try:
        n2, e2 = _extend_spare(best[0], best[1], d, D, deadline)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
