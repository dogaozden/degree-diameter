import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Program: Haar and bi-Cayley lifts over semidirect groups, searched in C.
#
# The C engine searches Z_M x| Z_K2 (r^K2 = 1 mod M) with K base blocks per side
# (K = 1 mostly, sometimes 2). Each graph is a lift: dart (layer l, block i) joins
# A_i,g to B_{lay[l][i]}, g*vol. Left translations are automorphisms, so the
# diameter test needs only one BFS per base block (from its identity element).
# Cost = total unreached pairs + penalty per parallel dart. Simulated annealing
# moves voltages and layer permutations. The target order ramps upward from the
# best valid graph found so far.
#
# Python side: exact constructions (PG(2,q), small W(q)) as start points, then
# the C search, then greedy slack extension. Every kept graph passes lib.is_valid.
# The fallback K_{d,d} is always valid for D >= 2.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXK 4
#define MAXDEG 32
#define PEN 20

static uint64_t rs;
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

static int DEG, DIAM, CAP;
static double TL, tstart;
static int K, K2, M, R, G, N;
static int64_t PWR[64];
static int *AA, *BB;
static int lay[MAXDEG * MAXK], vol[MAXDEG * MAXK], invlay[MAXDEG * MAXK];
static int *nbr, *bestnbr;
static int *vis, *q1;
static int vstamp;
static int64_t LASTCOST;
static int timed_out;
static int have_best, best_N, best_half;

static double elapsed(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    if (a < 0) a = -a;
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Choose a semidirect group Z_M x| Z_K2 of order G = M*K2 >= Gt. */
static int sample_group(int64_t Gt) {
    static const int K2C[] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 7, 8, 9, 10, 10,
                              12, 14, 16, 18, 20, 24, 30, 36};
    int nc = (int)(sizeof(K2C) / sizeof(K2C[0]));
    for (int attempt = 0; attempt < 100; attempt++) {
        int k2 = K2C[rndint(nc)];
        int64_t m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (k2 == 1) {
            M = (int)m;
            K2 = 1;
            R = 1;
            G = M;
            return 1;
        }
        int64_t r = -1;
        for (int tries = 0; tries < 60; tries++) {
            int64_t c;
            if (tries == 0) {
                c = (rnd01() < 0.2) ? 1 : (m - 1);
            } else if (tries == 1) {
                c = m - 1;
            } else {
                c = 2 + rndint((int)(m > 4 ? m - 3 : 1));
            }
            if (c < 1 || c >= m) continue;
            if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
        if (r < 0) continue;
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PWR[t] = powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + PWR[bx] * (int64_t)AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - (PWR[nb] * (int64_t)AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

/* Rebuild the full adjacency from lay/vol. A-vertex i*G+g has slot l -> B(lay, g*vol).
   B-vertex (K+j)*G+h has slot l -> A(invlay, h*vol^{-1}). */
static void build_graph(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) invlay[l * K + lay[l * K + i]] = i;
    for (int i = 0; i < K; i++) {
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int *row = nbr + (size_t)a * DEG;
            for (int l = 0; l < DEG; l++) {
                int j = lay[l * K + i];
                int s = vol[l * K + i];
                row[l] = (K + j) * G + gmul(g, s);
            }
        }
    }
    for (int j = 0; j < K; j++) {
        for (int h = 0; h < G; h++) {
            int b = (K + j) * G + h;
            int *row = nbr + (size_t)b * DEG;
            for (int l = 0; l < DEG; l++) {
                int i = invlay[l * K + j];
                int s = vol[l * K + i];
                int g = gmul(h, ginv(s));
                row[l] = i * G + g;
            }
        }
    }
}

/* Parallel darts: same target block and same voltage from the same A-block. */
static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++)
                if (lay[l1 * K + i] == lay[l2 * K + i] && vol[l1 * K + i] == vol[l2 * K + i])
                    dup++;
    return dup;
}

/* Number of vertices at distance > DIAM from source (BFS on the built lift). */
static int64_t bfs_unreached(int src) {
    if (vstamp == INT_MAX) {
        memset(vis, 0, sizeof(int) * (size_t)N);
        vstamp = 0;
    }
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    q1[tail++] = src;
    for (int lev = 0; lev < DIAM && head < tail; lev++) {
        int end = tail;
        for (; head < end; head++) {
            const int *nb = nbr + (size_t)q1[head] * DEG;
            for (int l = 0; l < DEG; l++) {
                int w = nb[l];
                if (vis[w] != vstamp) {
                    vis[w] = vstamp;
                    q1[tail++] = w;
                }
            }
        }
    }
    return (int64_t)(N - tail);
}

/* By left-translation symmetry, one identity source per base block suffices. */
static int64_t eval_cost(void) {
    int64_t c = 0;
    for (int b = 0; b < 2 * K; b++) c += bfs_unreached(b * G);
    return c;
}

static int64_t full_cost(void) {
    return eval_cost() + (int64_t)PEN * dupcount();
}

static int anneal(int reinit, int iters, int patience) {
    int n = DEG * K;
    timed_out = 0;
    if (reinit) {
        for (int l = 0; l < DEG; l++) {
            int perm[MAXK];
            for (int i = 0; i < K; i++) perm[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
            for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
        }
        for (int e = 0; e < n; e++) vol[e] = rndint(G);
    }
    build_graph();
    int64_t cost = full_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    int64_t best = cost;
    int last = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && elapsed() > TL) {
            timed_out = 1;
            break;
        }
        double temp = 0.08 * c0 * (1.0 - (double)t / iters) + 0.2;
        int64_t c2;
        if (K >= 2 && rnd01() < 0.2) {
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int a = l * K + i1, b = l * K + i2;
            int tp = lay[a];
            lay[a] = lay[b];
            lay[b] = tp;
            build_graph();
            c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tp = lay[a];
                lay[a] = lay[b];
                lay[b] = tp;
                build_graph();
            }
        } else {
            int e = rndint(n);
            int old = vol[e];
            int nw = rndint(G);
            if (nw == old) continue;
            vol[e] = nw;
            build_graph();
            c2 = full_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                vol[e] = old;
                build_graph();
            }
        }
        if (cost < best) {
            best = cost;
            last = t;
        }
    }
    LASTCOST = cost;
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D start_n cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long start_n = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3 || CAP < 8) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 1));
    BB = malloc(sizeof(int) * (size_t)(CAP + 1));
    vis = malloc(sizeof(int) * (size_t)(CAP + 1));
    q1 = malloc(sizeof(int) * (size_t)(CAP + 1));
    nbr = malloc(sizeof(int) * (size_t)DEG * (CAP + 1));
    bestnbr = malloc(sizeof(int) * (size_t)DEG * (CAP + 1));
    if (!AA || !BB || !vis || !q1 || !nbr || !bestnbr) {
        printf("0 0\n");
        return 0;
    }
    memset(vis, 0, sizeof(int) * (size_t)(CAP + 1));
    vstamp = 0;

    long long found = start_n;
    have_best = 0;

    while (elapsed() < TL) {
        if (found >= CAP) break;
        int k = (rnd01() < 0.75) ? 1 : 2;
        int64_t Gmin = ((int64_t)found + 1 + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        int64_t spanw = (rnd01() < 0.5) ? Gmin / 60 + 2 : Gmin / 12 + 2;
        int64_t Gt = Gmin + rndint((int)spanw);
        if (!sample_group(Gt)) continue;
        K = k;
        N = 2 * K * G;
        if (N <= found || N > CAP) continue;
        setup_group();

        int iters = 2000 + 3 * N;
        int patience = iters / 3 + 300;
        int ok = anneal(1, iters, patience);
        int extra = 0;
        while (!ok && !timed_out && extra < 2 && LASTCOST <= (int64_t)N / 4 && elapsed() < TL) {
            ok = anneal(0, iters, patience);
            extra++;
        }

        if (ok) {
            found = N;
            memcpy(bestnbr, nbr, sizeof(int) * (size_t)DEG * N);
            best_N = N;
            best_half = K * G;
            have_best = 1;
        }
        if (timed_out) break;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long long m = (long long)best_half * DEG;
    printf("%d %lld\n", best_N, m);
    for (int u = 0; u < best_half; u++)
        for (int l = 0; l < DEG; l++)
            printf("%d %d\n", u, bestnbr[(size_t)u * DEG + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
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
    """W(q) for a small prime power q with q + 1 <= d (kept small for Python speed)."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add vertices using spare degree, accepting only valid graphs.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return a 2-colouring of the graph, or None if it is not bipartite."""
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
# Main build: exact constructions, then the C lift search, then slack extension.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.82 * time_limit, time_limit - 9.0))
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3 and d >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and d >= 3 and time.monotonic() < start + 0.25 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 5 and lib.is_prime_power(d - 1):
                return best

    # Main search in C: semidirect-product lifts, annealed toward diameter D.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 15.0)
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
