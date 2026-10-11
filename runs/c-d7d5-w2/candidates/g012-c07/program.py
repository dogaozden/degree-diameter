import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: "grow-and-anneal" search over bi-Cayley lifts.
#
# Group: Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b), order G = m*k2.
# Base graph: K vertices per side and DEG layers. Layer l is a permutation of
# 0..K-1, so every vertex has degree DEG. Dart (l, i) joins A_i to B_{dJ}
# with voltage dS: A_{i,g} ~ B_{j, g*s} for all g. Vertex count is 2*K*G.
#
# NEW in this version: base growth. Once an anneal finds a valid lift at size
# K, the engine keeps it and grows the base to K+1 by adding one A vertex and
# one B vertex per layer. The new dart in each layer joins A_K to B_K with a
# random voltage, so every layer stays a permutation. The annealer then repairs
# the grown lift, starting from the valid lift it just came from. The chain
# runs from Kmin up to Kmax and outputs the largest valid K reached.
#
# Cost: excess-distance BFS from the 2K representatives (left multiplication is
# a group automorphism, so these decide the diameter exactly). A vertex at
# distance t > DIAM costs (t - DIAM). An unreached vertex costs
# (LMAX - DIAM + 2). Duplicate darts are penalised.
#
# Moves: change a voltage, or swap the targets of two darts in one layer.
#
# Usage: prog d D Kmin Kmax m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000
#define RL 60000

static int DEG, DIAM, KMAX, K, MM, K2, G, N, NE, NEMAX, NMAX;
static int *POWR;
/* Darts are stored with stride KMAX: index l*KMAX + i. */
static int *dJ, *dS, *bJ, *bS, *vJ, *vS;
static int *perm, *adj, *cnt, *fr, *nx, *pbuf;
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

static void set_perm(int idx) {
    int s = dS[idx];
    int *pm = perm + (size_t)idx * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static void set_all_perms(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) set_perm(l * KMAX + i);
}

static void save_best(void) {
    memcpy(bJ, dJ, sizeof(int) * (size_t)NEMAX);
    memcpy(bS, dS, sizeof(int) * (size_t)NEMAX);
}

/* Excess-distance cost. Zero iff the lift has diameter <= DIAM and no dup darts. */
static int cost_fn(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++) {
                int e1 = l1 * KMAX + i, e2 = l2 * KMAX + i;
                if (dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;
            }

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int e = l * KMAX + i;
            int ba = i * G, bb = (K + dJ[e]) * G;
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
            memset(vis, 0, sizeof(uint32_t) * (size_t)NMAX);
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

/* Fresh random lift at the current K. */
static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) pbuf[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pbuf[i]; pbuf[i] = pbuf[j]; pbuf[j] = t;
        }
        for (int i = 0; i < K; i++) dJ[l * KMAX + i] = pbuf[i];
    }
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) dS[l * KMAX + i] = rndint(G);
    set_all_perms();
}

/* Grow the base from K to K+1 in place. Each layer gets a dart A_K -> B_K,
   so every layer remains a permutation and all degrees stay DEG. */
static void grow_state(void) {
    for (int l = 0; l < DEG; l++) {
        int e = l * KMAX + K;
        dJ[e] = K;
        dS[e] = rndint(G);
    }
    K++;
    N = 2 * K * G;
    NE = DEG * K;
    for (int l = 0; l < DEG; l++) set_perm(l * KMAX + K - 1);
}

/* Anneal at the current K. Returns 1 with a valid state in dJ/dS, or 0 at timeout. */
static int level_search(clock_t t0, double slice, int from_grown) {
    int bestCost = BIGCOST;
    int first = 1;
    while (elapsed(t0) < slice) {
        double T0;
        if (first && from_grown) {
            T0 = 1.0;
        } else if (bestCost >= BIGCOST || rnd01() < 0.25) {
            random_init();
            T0 = 2.0;
        } else {
            memcpy(dJ, bJ, sizeof(int) * (size_t)NEMAX);
            memcpy(dS, bS, sizeof(int) * (size_t)NEMAX);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) {
                int l = rndint(DEG), i = rndint(K);
                dS[l * KMAX + i] = rndint(G);
            }
            set_all_perms();
            T0 = 0.8;
        }
        first = 0;
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) return 1;

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
                int e1 = l * KMAX + i1, e2 = l * KMAX + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(DEG) * KMAX + rndint(K);
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
            if (cur == 0) return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 10) {
        fprintf(stderr, "usage: prog d D Kmin Kmax m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int Kmin = atoi(argv[3]);
    KMAX = atoi(argv[4]);
    MM = atoi(argv[5]);
    K2 = atoi(argv[6]);
    int r = atoi(argv[7]);
    uint64_t seed = strtoull(argv[8], NULL, 10);
    double slice = atof(argv[9]);

    if (DEG < 1 || DIAM < 1 || Kmin < 1 || KMAX < Kmin || MM < 1 || K2 < 1 || K2 > 4096) {
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
    NMAX = 2 * KMAX * G;
    NEMAX = DEG * KMAX;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dJ = malloc(sizeof(int) * (size_t)NEMAX);
    dS = malloc(sizeof(int) * (size_t)NEMAX);
    bJ = malloc(sizeof(int) * (size_t)NEMAX);
    bS = malloc(sizeof(int) * (size_t)NEMAX);
    vJ = malloc(sizeof(int) * (size_t)NEMAX);
    vS = malloc(sizeof(int) * (size_t)NEMAX);
    perm = malloc(sizeof(int) * (size_t)NEMAX * G);
    adj = malloc(sizeof(int) * (size_t)NMAX * DEG);
    cnt = malloc(sizeof(int) * (size_t)NMAX);
    fr = malloc(sizeof(int) * (size_t)NMAX);
    nx = malloc(sizeof(int) * (size_t)NMAX);
    vis = calloc((size_t)NMAX, sizeof(uint32_t));
    pbuf = malloc(sizeof(int) * (size_t)KMAX);
    if (!dJ || !dS || !bJ || !bS || !vJ || !vS || !perm || !adj || !cnt ||
        !fr || !nx || !vis || !pbuf) {
        printf("0 0\n");
        return 0;
    }
    memset(dJ, 0, sizeof(int) * (size_t)NEMAX);
    memset(dS, 0, sizeof(int) * (size_t)NEMAX);

    K = Kmin;
    N = 2 * K * G;
    NE = DEG * K;

    clock_t t0 = clock();
    int validK = 0;
    int fromGrown = 0;
    while (1) {
        if (!level_search(t0, slice, fromGrown)) break;
        validK = K;
        memcpy(vJ, dJ, sizeof(int) * (size_t)NEMAX);
        memcpy(vS, dS, sizeof(int) * (size_t)NEMAX);
        if (K >= KMAX) break;
        grow_state();
        fromGrown = 1;
    }

    if (validK == 0) {
        printf("0 0\n");
        fflush(stdout);
        return 0;
    }

    K = validK;
    N = 2 * K * G;
    NE = DEG * K;
    memcpy(dJ, vJ, sizeof(int) * (size_t)NEMAX);
    memcpy(dS, vS, sizeof(int) * (size_t)NEMAX);
    set_all_perms();

    printf("%d %d\n", N, NE * G);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int e = l * KMAX + i;
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", i * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
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
# Greedy spare-degree extension (unchanged): add a fresh vertex pair while the
# graph stays valid. Regular lifts have no spare degree, so this is a no-op.
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
# Group sampling and the search driver.
# ----------------------------------------------------------------------------

K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _pick_group(gmin, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= gmin, or None.

    r = 1 (direct product) is always valid. A nontrivial twist is preferred
    most of the time, since twisted groups tend to give better lifts.
    """
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m0 = max(2, -(-gmin // k2))
        m = m0 + rng.randrange(0, 6)
        if m > 4000:
            continue
        twists = [c for c in range(2, m)
                  if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if twists and rng.random() < 0.7:
            return m, k2, rng.choice(twists)
        return m, k2, 1
    return None


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

    # Main search. Each C call grows a base chain from K = 1 up to kmax.
    step = 0.08
    while True:
        remaining = search_deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 15.0)
        kf = rng.choice([2, 3, 3, 4, 4, 5])
        want = best[0] * (1.0 + step)
        gmin = max(2, math.ceil(want / (2 * kf)))
        grp = _pick_group(gmin, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G = m * k2
        kmax = min(12, max(2, math.ceil(want / (2 * G)) + 1))
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, 1, kmax, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
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
