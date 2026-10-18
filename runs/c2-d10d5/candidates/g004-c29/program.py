"""Bi-Cayley lift search, version 3: reheated annealing from the best state.

Changes from the parent:
- The C engine is an iterated annealer. Each cycle restarts from the best state
  found so far, with a reheat scaled to its cost, instead of from random layers.
- Group family is wider: semidirect products Z_m x| Z_k2 with every valid action r,
  including the abelian (r = 1) and dihedral-type cases, for k2 up to 24.
- Base size k runs from 1 to 6 blocks per side.
- Exact constructions (projective plane, generalized quadrangle) and K_{d,d}
  remain as fallbacks, so every returned graph is valid.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define PEN 1000L

static int d, D, k, m, k2, r, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int bestL[MAXD][MAXK];
static int bestS[MAXD][MAXK];
static int *nbr;
static uint16_t *bufA, *bufB, *resbuf, *accreach;
static int powr[64];
static unsigned char pop16[65536];
static uint64_t RS = 88172645463325252ULL;

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group element x = a*k2 + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)powr[b] * c;
    int aa = (int)(t % m);
    int bb = b + e;
    if (bb >= k2) bb -= k2;
    return aa * k2 + bb;
}

/* Dart (l, i): A-block i joins B-block layers[l][i] with voltage S[l][i]. */
static void set_dart(int l, int i) {
    int j = layers[l][i], s = S[l][i];
    for (int g = 0; g < G; g++) {
        int u = i * G + g;
        int w = (k + j) * G + gmul(g, s);
        nbr[(size_t)u * d + l] = w;
        nbr[(size_t)w * d + l] = u;
    }
}

static void set_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
}

static void restore_best(void) {
    memcpy(layers, bestL, sizeof layers);
    memcpy(S, bestS, sizeof S);
    set_all();
}

static void save_best(void) {
    memcpy(bestL, layers, sizeof layers);
    memcpy(bestS, S, sizeof S);
}

/* Unreached (block representative, vertex) pairs. Result of the last call is in resbuf. */
static long eval_cost(void) {
    int NB = 2 * k;
    uint16_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < NB; b++) cur[(size_t)b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            const int *nv = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nv[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += NB - pop16[cur[v]];
    memcpy(resbuf, cur, sizeof(uint16_t) * (size_t)N);
    return unreached;
}

/* Number of block-level duplicate darts (same target block and same voltage). */
static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layers[l1][i] == layers[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static long eval_full(void) { return eval_cost() + PEN * dupcount(); }

static void accept_reach(void) {
    memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    long iters = atol(argv[9]);
    if (iters < 500) iters = 500;

    if (d < 1 || d > MAXD || k < 1 || k > MAXK || D < 1 || m < 1 || k2 < 1 || k2 > 63 || r < 0) {
        printf("0 0\n");
        return 0;
    }
    if (m > 100000 || (long long)m * k2 > 200000LL) { printf("0 0\n"); return 0; }
    r %= m;
    if (gcd_int(r, m) != 1 && m > 1) { printf("0 0\n"); return 0; }
    G = m * k2;
    N = 2 * k * G;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k2 - 1] * r) % m != (1 % m)) { printf("0 0\n"); return 0; }

    for (int x = 1; x < 65536; x++) pop16[x] = (unsigned char)(pop16[x >> 1] + (x & 1));
    nbr = malloc(sizeof(int) * (size_t)N * (size_t)d);
    bufA = malloc(sizeof(uint16_t) * (size_t)N);
    bufB = malloc(sizeof(uint16_t) * (size_t)N);
    resbuf = malloc(sizeof(uint16_t) * (size_t)N);
    accreach = malloc(sizeof(uint16_t) * (size_t)N);
    if (!nbr || !bufA || !bufB || !resbuf || !accreach) { printf("0 0\n"); return 0; }

    RS = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (RS == 0) RS = 88172645463325252ULL;
    for (int w = 0; w < 10; w++) rnd64();

    double tend = now_s() + tl;
    uint16_t full = (uint16_t)((1u << (2 * k)) - 1u);

    /* Random start. */
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
    }
    set_all();
    long cost = eval_full();
    accept_reach();
    save_best();
    long bestcost = cost;

    /* Iterated annealing: each cycle reheats from the best state found so far. */
    long cycle = 0;
    while (bestcost != 0 && now_s() < tend) {
        if (cycle > 0) {
            restore_best();
            cost = eval_full();
            accept_reach();
        }
        double c0 = (double)(cost > 1 ? cost : 1);
        double T0 = 1.0 + 0.05 * c0;

        for (long t = 0; t < iters && cost != 0; t++) {
            if ((t & 31) == 0 && now_s() > tend) break;
            double temp = T0 * (1.0 - (double)t / (double)iters);
            if (temp < 0.3) temp = 0.3;

            if (k >= 2 && rnd01() < 0.25) {
                int l = rndint(d);
                int i1 = rndint(k);
                int i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
                long c2 = eval_full();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                    accept_reach();
                } else {
                    tmp = layers[l][i1];
                    layers[l][i1] = layers[l][i2];
                    layers[l][i2] = tmp;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
            } else {
                int l = rndint(d);
                int i = rndint(k);
                if (rnd01() < 0.4) {
                    /* Defect-targeted: a uniformly random unreached (vertex, block) owner. */
                    int nb = 0, pick = -1;
                    for (int v = 0; v < N; v++) {
                        if (accreach[v] != full) {
                            nb++;
                            if (rndint(nb) == 0) pick = v;
                        }
                    }
                    if (pick >= 0) {
                        int block = pick / G;
                        if (block < k) {
                            i = block;
                        } else {
                            int j = block - k;
                            for (int q = 0; q < k; q++)
                                if (layers[l][q] == j) { i = q; break; }
                        }
                    }
                }
                int old = S[l][i];
                int nw = rndint(G);
                if (nw != old) {
                    S[l][i] = nw;
                    set_dart(l, i);
                    long c2 = eval_full();
                    if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                        cost = c2;
                        accept_reach();
                    } else {
                        S[l][i] = old;
                        set_dart(l, i);
                    }
                }
            }
            if (cost < bestcost) {
                bestcost = cost;
                save_best();
            }
        }
        cycle++;
    }

    if (bestcost != 0) { printf("0 0\n"); return 0; }
    restore_best();
    int A = k * G;
    printf("%d %ld\n", N, (long)A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)u * d + l]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (safe fallbacks).
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
                for r_ in L:
                    if p < r_:
                        covered.add((p, r_))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9."""
    for q in range(min(d - 1, 9), 1, -1):
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
# Bi-Cayley lifts over Z_m x| Z_k2, searched by the C engine.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        cands = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _c_search(d, D, k, m, k2, r, seed, slice_s):
    """Run the C annealer on one group for about slice_s seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, round(slice_s, 3), 4000],
                    stdin_graph=None, timeout=slice_s + 8.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    final_deadline = t0 + max(1.0, time_limit - 3.0)
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

    # Ladder search: bandit over base sizes k; each success raises the target.
    KS = (1, 2, 3, 4, 5, 6)
    trials = {kk: 0 for kk in KS}
    wins = {kk: 0 for kk in KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(KS)
        return max(KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())

    slice_target = max(1.5, budget / 10.0)
    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            continue
        trials[k] += 1
        slice_s = min(deadline - time.monotonic(), slice_target)
        if slice_s < 0.5:
            break
        try:
            res = _c_search(d, D, k, m, k2, r, rng.randrange(1 << 30), slice_s)
        except (RuntimeError, ValueError, OSError):
            break
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
