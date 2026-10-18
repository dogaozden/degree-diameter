import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold variant: random d-regular bipartite graphs with annealed diameter repair.
#
# This replaces the bi-Cayley voltage search with a non-algebraic construction.
# The C engine:
#   - starts from a circulant d-regular bipartite graph on N+N vertices,
#   - randomises it with degree-preserving double edge swaps,
#   - anneals the swaps to minimise the number of vertex pairs at distance > D
#     (computed with bitset ball expansion),
#   - when the cost reaches 0 it saves the graph and grows it by one vertex per
#     side (remove d disjoint edges a_k-b_k, add a'-b_k and a_k-b'), keeping
#     all degrees equal to d and the graph bipartite.
#
# Every candidate passes lib.is_valid. The exact PG(2,q) and W(q) constructions
# and the K_{d,d} fallback are kept as safe starting points.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAPN 2100
#define MAXD 16
#define MAXW ((2 * CAPN + 63) / 64)
#define STALL 3000
#define TEMP 0.5

static int DEG, DIAM, N;
static double TL, tstart;
static uint64_t rs;

static int nb[2 * CAPN][MAXD];
static uint64_t cur[2 * CAPN][MAXW];
static uint64_t nxt[2 * CAPN][MAXW];
static int bestnb[2 * CAPN][MAXD];
static int bestN = 0;

static int SA1, SB1, SA2, SB2;

static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

/* active vertex k: A side k in 0..N-1 -> label k; B side k -> label CAPN + (k - N) */
static inline int LBL(int k) {
    return k < N ? k : CAPN + (k - N);
}

static inline int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_nb(int x, int y) {
    for (int l = 0; l < DEG; l++)
        if (nb[x][l] == y) return 1;
    return 0;
}

static void replace_nb(int x, int old, int nw) {
    for (int l = 0; l < DEG; l++) {
        if (nb[x][l] == old) {
            nb[x][l] = nw;
            return;
        }
    }
}

/* edges a1-b1, a2-b2 become a1-b2, a2-b1 (degree preserving) */
static void swap4(int a1, int b1, int a2, int b2) {
    replace_nb(a1, b1, b2);
    replace_nb(b1, a1, a2);
    replace_nb(a2, b2, b1);
    replace_nb(b2, a2, a1);
}

static int pick_swap(void) {
    int a1 = rndint(N), l1 = rndint(DEG);
    int b1 = nb[a1][l1];
    int a2 = rndint(N), l2 = rndint(DEG);
    int b2 = nb[a2][l2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_nb(a1, b2) || has_nb(a2, b1)) return 0;
    SA1 = a1;
    SB1 = b1;
    SA2 = a2;
    SB2 = b2;
    return 1;
}

static void init_circ(void) {
    for (int i = 0; i < N; i++)
        for (int s = 0; s < DEG; s++)
            nb[i][s] = CAPN + (i + s) % N;
    for (int j = 0; j < N; j++)
        for (int s = 0; s < DEG; s++)
            nb[CAPN + j][s] = (j - s + N) % N;
}

/* number of ordered vertex pairs at distance > DIAM (0 iff valid diameter) */
static int64_t eval_cost(void) {
    int W = (CAPN + N + 63) / 64;
    int V = 2 * N;
    for (int k = 0; k < V; k++) {
        int x = LBL(k);
        memset(cur[x], 0, sizeof(uint64_t) * (size_t)W);
        cur[x][x >> 6] |= 1ULL << (x & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int k = 0; k < V; k++) {
            int x = LBL(k);
            uint64_t *out = nxt[x];
            memcpy(out, cur[x], sizeof(uint64_t) * (size_t)W);
            for (int l = 0; l < DEG; l++) {
                const uint64_t *src = cur[nb[x][l]];
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
            if (memcmp(out, cur[x], sizeof(uint64_t) * (size_t)W) != 0) changed = 1;
        }
        if (!changed) break;
        for (int k = 0; k < V; k++) {
            int x = LBL(k);
            memcpy(cur[x], nxt[x], sizeof(uint64_t) * (size_t)W);
        }
    }
    int64_t cost = 0;
    for (int k = 0; k < V; k++) {
        int x = LBL(k);
        int pop = 0;
        for (int w = 0; w < W; w++) pop += pc64(cur[x][w]);
        cost += V - pop;
    }
    return cost;
}

/* add one vertex per side, keeping every degree equal to DEG */
static int grow(void) {
    if (N + 1 > CAPN) return 0;
    int ta[MAXD], tb[MAXD];
    int cnt = 0;
    for (int tries = 0; cnt < DEG && tries < 200000; tries++) {
        int a = rndint(N), l = rndint(DEG);
        int b = nb[a][l];
        int ok = 1;
        for (int k = 0; k < cnt; k++) {
            if (ta[k] == a || tb[k] == b) {
                ok = 0;
                break;
            }
        }
        if (ok) {
            ta[cnt] = a;
            tb[cnt] = b;
            cnt++;
        }
    }
    if (cnt < DEG) return 0;
    int na = N, nbl = CAPN + N;
    for (int k = 0; k < DEG; k++) {
        replace_nb(ta[k], tb[k], nbl);
        replace_nb(tb[k], ta[k], na);
        nb[na][k] = tb[k];
        nb[nbl][k] = ta[k];
    }
    N++;
    return 1;
}

static void save_best(void) {
    bestN = N;
    for (int k = 0; k < N; k++) {
        memcpy(bestnb[k], nb[k], sizeof(nb[k]));
        memcpy(bestnb[CAPN + k], nb[CAPN + k], sizeof(nb[CAPN + k]));
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    TL = atof(argv[4]);
    if (DEG < 3 || DEG > MAXD || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }
    tstart = (double)clock() / CLOCKS_PER_SEC;
    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    N = DEG + 1;
    init_circ();
    for (long t = 0; t < 20L * N * DEG; t++) {
        if (pick_swap()) swap4(SA1, SB1, SA2, SB2);
    }

    int64_t cost = eval_cost();
    int64_t bestc = cost;
    long stall = 0;
    long it = 0;

    while (1) {
        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_cost();
            bestc = cost;
            stall = 0;
            continue;
        }
        if ((it++ & 15) == 0 && elapsed() > TL) break;
        if (!pick_swap()) continue;
        swap4(SA1, SB1, SA2, SB2);
        int64_t c2 = eval_cost();
        int64_t delta = c2 - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / TEMP)) {
            cost = c2;
        } else {
            swap4(SA1, SB2, SA2, SB1);
        }
        if (cost < bestc) {
            bestc = cost;
            stall = 0;
        } else if (++stall > STALL) {
            for (int k = 0; k < 12; k++) {
                if (pick_swap()) swap4(SA1, SB1, SA2, SB2);
            }
            cost = eval_cost();
            bestc = cost;
            stall = 0;
        }
    }

    if (!bestN) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)bestN * DEG;
    printf("%d %ld\n", 2 * bestN, m);
    for (int i = 0; i < bestN; i++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", i, bestN + (bestnb[i][l] - CAPN));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as safe starting graphs.
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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build: exact constructions first, then the C annealing search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

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

    # Exact constructions; return immediately on calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: random regular bipartite graph repaired and grown in C.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 5.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
