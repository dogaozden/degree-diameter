import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of voltage lifts over several base vertices, search
# directly for BI-CAYLEY graphs (one base vertex per side).
#
# Group: G = Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b), |G| = m*k2.
# Vertices: A_g = g and B_g = G + g. Edges: A_g ~ B_{g*s} for each s in S,
# where S is a set of exactly DEG distinct group elements. This is DEG-regular
# and bipartite, and it has 2|G| vertices.
#
# Left multiplication by h maps A_g -> A_{hg}, B_g -> B_{hg} and preserves
# edges, so the graph is transitive on each side. Hence the diameter is at
# most DIAM iff BFS from A_1 and from B_1 both reach every vertex within DIAM
# steps. Each cost evaluation is therefore two small BFS runs.
#
# C engine: simulated annealing over the set S, with cost = number of vertices
# not reached within DIAM from A_1 plus from B_1. Cost 0 gives a valid graph.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC (1 << 30)
#define RL 40000
#define GMAX 2500

static int DEG, DIAM, MM, K2, G, N;
static int *POWR, *MUL, *INV;
static int *S, *IS, *bestS, *inS;
static uint32_t *vis;
static int *bufA, *bufB;
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

/* Number of vertices NOT reached within DIAM steps from src. */
static int bfs_unreached(int src) {
    stamp++;
    if (stamp == 0) {
        memset(vis, 0, sizeof(uint32_t) * (size_t)N);
        stamp = 1;
    }
    int *cur = bufA, *nxt = bufB;
    int cn = 1, reached = 1;
    cur[0] = src;
    vis[src] = stamp;
    for (int lv = 0; lv < DIAM && cn > 0; lv++) {
        int nn = 0;
        for (int q = 0; q < cn; q++) {
            int u = cur[q];
            if (u < G) {
                const int *row = MUL + (size_t)u * G;
                for (int i = 0; i < DEG; i++) {
                    int v = G + row[S[i]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            } else {
                const int *row = MUL + (size_t)(u - G) * G;
                for (int i = 0; i < DEG; i++) {
                    int v = row[IS[i]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                }
            }
        }
        reached += nn;
        int *t = cur; cur = nxt; nxt = t;
        cn = nn;
    }
    return N - reached;
}

static int cost_fn(void) {
    return bfs_unreached(0) + bfs_unreached(G);
}

static void load_state(const int *src) {
    memset(inS, 0, sizeof(int) * (size_t)G);
    for (int i = 0; i < DEG; i++) {
        S[i] = src[i];
        inS[src[i]] = 1;
        IS[i] = INV[src[i]];
    }
}

static void replace_at(int i, int x) {
    inS[S[i]] = 0;
    S[i] = x;
    inS[x] = 1;
    IS[i] = INV[x];
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G < DEG + 1 || G > GMAX) { printf("0 0\n"); return 0; }
    N = 2 * G;
    r %= MM;
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MUL = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * DEG);
    IS = malloc(sizeof(int) * DEG);
    bestS = malloc(sizeof(int) * DEG);
    inS = malloc(sizeof(int) * G);
    vis = calloc((size_t)N, sizeof(uint32_t));
    bufA = malloc(sizeof(int) * N);
    bufB = malloc(sizeof(int) * N);
    if (!MUL || !INV || !S || !IS || !bestS || !inS || !vis || !bufA || !bufB) {
        printf("0 0\n");
        return 0;
    }

    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, dd = y % K2;
            long long t = ((long long)a + (long long)POWR[b] * c) % MM;
            MUL[(size_t)x * G + y] = (int)(t * K2 + (b + dd) % K2);
        }
    }
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        int nb = (K2 - b) % K2;
        long long ia = ((long long)MM - ((long long)POWR[nb] * a) % MM) % MM;
        INV[x] = (int)(ia * K2 + nb);
    }
    for (int x = 0; x < G; x++) {
        if (MUL[(size_t)x * G + INV[x]] != 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x7654321ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    int bestc = BIGC;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestc < BIGC && rnd01() < 0.5) {
            load_state(bestS);
            for (int k = 0; k < 2; k++) {
                int i = rndint(DEG);
                int x = rndint(G);
                if (!inS[x]) replace_at(i, x);
            }
            T0 = 0.6;
        } else {
            memset(inS, 0, sizeof(int) * (size_t)G);
            int cnt = 0;
            while (cnt < DEG) {
                int x = rndint(G);
                if (!inS[x]) {
                    inS[x] = 1;
                    S[cnt] = x;
                    IS[cnt] = INV[x];
                    cnt++;
                }
            }
            T0 = 1.5;
        }

        int cur = cost_fn();
        if (cur < bestc) { bestc = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 511) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.03;
            int i = rndint(DEG);
            int x = rndint(G);
            if (inS[x]) continue;
            int old = S[i];
            replace_at(i, x);
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestc) { bestc = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
                if (cur == 0) { found = 1; break; }
            } else {
                replace_at(i, old);
            }
        }
    }

    if (found) {
        printf("%d %d\n", N, G * DEG);
        for (int g = 0; g < G; g++) {
            for (int i = 0; i < DEG; i++) {
                printf("%d %d\n", g, G + MUL[(size_t)g * G + S[i]]);
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
# Exact / safe constructions (unchanged from the parent).
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
# Spare-degree extension (unchanged): usually a no-op for regular graphs.
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
# Bi-Cayley search driver.
# ----------------------------------------------------------------------------

def _group_options(G, rng):
    """All (m, k2, r) with m * k2 = G and Z_m x|_r Z_k2 a valid semidirect product, shuffled."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        rs = [1]
        if k2 > 1 and m > 2:
            rs += [c for c in range(2, m)
                   if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        for r in rs:
            opts.append((m, k2, r))
    rng.shuffle(opts)
    return opts


def _cayley_search(d, D, best, rng, deadline):
    """Climb the bi-Cayley order G = |group| while the C annealer finds valid graphs.

    The graph has 2G vertices. Each success raises the target order; failures
    shrink the step toward +1 but never go below the current best.
    """
    cur_best = best
    G = cur_best[0] // 2 + 1
    bump = max(1, G // 60)
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.5:
            break
        if G < d + 1:
            G = d + 1
        opts = _group_options(G, rng)
        if not opts:
            G += 1
            continue
        got = None
        for (m, k2, r) in opts[:2]:
            remaining = deadline - time.monotonic()
            s = min(remaining - 1.5, 6.0)
            if s < 0.5:
                break
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{s:.2f}"],
                    timeout=s + 10.0,
                )
            except RuntimeError:
                return cur_best  # compile or runtime failure: keep the safe graph
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            if n > cur_best[0] and lib.is_valid(n, e, d, D):
                got = (n, e)
                break
        if got is not None:
            cur_best = got
            G = got[0] // 2 + bump
            bump = min(bump * 2, max(1, G // 25))
        else:
            bump = max(1, bump // 2)
            G = cur_best[0] // 2 + bump
    return cur_best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 4.5))
    deadline = start + budget
    search_deadline = start + 0.93 * budget
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

    # Exact constructions.
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

    # Bold change: bi-Cayley annealing over group sets, replacing voltage lifts.
    if d >= 2 and time.monotonic() < search_deadline - 2.0:
        try:
            best = _cayley_search(d, D, best, rng, search_deadline)
        except Exception:
            pass

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
