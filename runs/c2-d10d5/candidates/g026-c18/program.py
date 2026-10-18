import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Program: single-orbit bi-Cayley search over semidirect groups Z_m x| Z_k.
#
# Bold change from the parent: instead of multi-base voltage lifts, the C engine
# searches a single bipartite Cayley-type graph on A = G x {0} and B = G x {1}
# with edges a_g ~ b_{g s} for s in a connection set S of size d. Left
# translations are automorphisms, so the diameter equals max(ecc(a_e), ecc(b_e)).
# That gives a cheap exact check: two BFS runs per move, with no group-wide
# all-pairs work. The search runs simulated annealing on S for a group chosen
# at random, and grows the group order one step past the best found so far.
#
# Python keeps the exact constructions (PG(2,q), W(q)) as the start point, a
# Haar-graph fallback, and greedy slack extension. Every output passes lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 32
#define NK 24

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
static int M, K2, R, G, NV;
static int *AA, *BB, *dist, *queue;
static int PW[64];
static int S[MAXDEG], SI[MAXDEG];

static const int K2C[NK] = {1,1,1,2,2,2,3,3,4,4,5,6,6,7,8,8,9,10,12,14,15,16,18,24};

static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int sample_group(int64_t target) {
    for (int att = 0; att < 200; att++) {
        int k2 = K2C[rndint(NK)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int64_t r = -1;
        if (k2 == 1 || rnd01() < 0.2) {
            r = 1;
        } else {
            for (int tr = 0; tr < 80 && m > 3; tr++) {
                int64_t c = 2 + rndint((int)(m - 3));
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) r = 1;
        }
        M = (int)m;
        K2 = k2;
        R = (int)r;
        G = M * K2;
        NV = 2 * G;
        if (NV > CAP) continue;
        return 1;
    }
    return 0;
}

static void setup_group(void) {
    for (int t = 0; t < K2; t++) PW[t] = (int)powmod(R, t, M);
    for (int x = 0; x < G; x++) {
        AA[x] = x / K2;
        BB[x] = x % K2;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e), element (a,b) coded as a*K2 + b */
static inline int gmul(int x, int y) {
    int bx = BB[x];
    int64_t a2 = (AA[x] + (int64_t)PW[bx] * AA[y]) % M;
    int b2 = (bx + BB[y]) % K2;
    return (int)(a2 * K2 + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int b = BB[x];
    int nb = (K2 - b) % K2;
    int64_t a2 = (M - ((int64_t)PW[nb] * AA[x]) % M) % M;
    return (int)(a2 * K2 + nb);
}

static void init_S(void) {
    for (int j = 0; j < DEG; j++) {
        int x, ok;
        do {
            x = rndint(G);
            ok = 1;
            for (int q = 0; q < j; q++)
                if (S[q] == x) {
                    ok = 0;
                    break;
                }
        } while (!ok);
        S[j] = x;
        SI[j] = ginv(x);
    }
}

/* Unreached vertices from src, within DIAM steps. Vertices: a_g = g, b_h = G + h. */
static int bfs_cost(int src) {
    memset(dist, 0xff, sizeof(int) * (size_t)NV);
    int qh = 0, qt = 0;
    dist[src] = 0;
    queue[qt++] = src;
    while (qh < qt) {
        int v = queue[qh++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < G) {
            for (int j = 0; j < DEG; j++) {
                int w = G + gmul(v, S[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    queue[qt++] = w;
                }
            }
        } else {
            int h = v - G;
            for (int j = 0; j < DEG; j++) {
                int w = gmul(h, SI[j]);
                if (dist[w] < 0) {
                    dist[w] = dv + 1;
                    queue[qt++] = w;
                }
            }
        }
    }
    return NV - qt;
}

static int64_t eval_cost(void) {
    return (int64_t)bfs_cost(0) + (int64_t)bfs_cost(G);
}

/* Simulated annealing on S. Returns 1 if the diameter bound holds. */
static int trial(int iters, int64_t *out_cost) {
    int64_t cost = eval_cost();
    int64_t c0 = cost > 1 ? cost : 1;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 255) == 0 && now() > TL) break;
        double temp = 0.03 * (double)c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;
        int j = rndint(DEG);
        int x = rndint(G);
        int dup = 0;
        for (int q = 0; q < DEG; q++)
            if (S[q] == x) {
                dup = 1;
                break;
            }
        if (dup) continue;
        int old = S[j], oldi = SI[j];
        S[j] = x;
        SI[j] = ginv(x);
        int64_t c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            S[j] = old;
            SI[j] = oldi;
        }
    }
    *out_cost = cost;
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best0 cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    CAP = atoi(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 2 || DEG > MAXDEG || DIAM < 2 || CAP < 2 * DEG + 4) {
        printf("0 0\n");
        return 0;
    }

    AA = malloc(sizeof(int) * (size_t)(CAP + 2));
    BB = malloc(sizeof(int) * (size_t)(CAP + 2));
    dist = malloc(sizeof(int) * (size_t)(CAP + 2));
    queue = malloc(sizeof(int) * (size_t)(CAP + 2));
    if (!AA || !BB || !dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    long long found = best0;
    int have = 0;
    int bM = 0, bK = 0, bR = 0;
    int bS[MAXDEG];

    while (now() < TL) {
        if (found >= CAP) break;
        int64_t base = found / 2;
        int64_t span = base / 20 + 2;
        int64_t target = base + 1 + rndint((int)span);
        if (!sample_group(target)) continue;
        if (NV <= found || NV > CAP || G < DEG + 1) continue;
        setup_group();
        init_S();
        int ok = 0;
        int64_t cost = 0;
        for (int tr = 0; tr < 3 && !ok && now() < TL; tr++) {
            ok = trial(30000, &cost);
        }
        if (ok) {
            found = NV;
            have = 1;
            bM = M;
            bK = K2;
            bR = R;
            memcpy(bS, S, sizeof(int) * (size_t)DEG);
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    M = bM;
    K2 = bK;
    R = bR;
    G = M * K2;
    NV = 2 * G;
    setup_group();
    memcpy(S, bS, sizeof(int) * (size_t)DEG);
    printf("%d %lld\n", NV, (long long)G * DEG);
    for (int g = 0; g < G; g++)
        for (int j = 0; j < DEG; j++)
            printf("%d %d\n", g, G + gmul(g, S[j]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as the start graph.
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
# Main build: exact constructions first, then the C Cayley-type search, then slack.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact constructions: return immediately on calibration-style cases.
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

    # Main search, entirely in C: single-orbit bi-Cayley graphs over Z_m x| Z_k.
    if d >= 3 and D >= 3:
        remaining = start + budget - time.monotonic()
        if remaining > 2.0:
            cap = lib.moore_bound(d, D)
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                                 timeout=remaining + 20.0)
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
