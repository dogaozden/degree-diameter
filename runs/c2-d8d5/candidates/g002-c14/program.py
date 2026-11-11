import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts on Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, G = m*k2.
# Layer l pairs A_i with B_{lay[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Each layer is a perfect matching, so every vertex has degree d exactly when
# there are no duplicate darts (same i, same j, same s), which the cost penalises.
# Left multiplication is an automorphism, so checking the K-block representatives
# from every vertex is exact for the diameter.
#
# Usage: prog d D K m k2 r seed time_ms
# Prints "n m" plus edges on success, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 15
#define MAXK2 64
#define PEN 1000

static int d, D, K, M, K2, R, G, N;
static int pw[MAXK2];
static int *invT;
static int lay[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int *nbr;
static uint32_t *curR, *trialR;
static uint64_t rs;
static clock_t t0;
static long long limit_ms;

static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static long long elapsed_ms(void) {
    return (long long)((double)(clock() - t0) * 1000.0 / CLOCKS_PER_SEC);
}

static int popc(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)pw[b] * c) % M;
    return (int)t * K2 + (b + e) % K2;
}

static void set_dart(int l, int i) {
    int j = lay[l][i], s = Sv[l][i];
    int *nb = nbr + (size_t)l * N;
    int sinv = invT[s];
    for (int g = 0; g < G; g++)
        nb[i * G + g] = (K + j) * G + gmul(g, s);
    for (int h = 0; h < G; h++)
        nb[(K + j) * G + h] = i * G + gmul(h, sinv);
}

static long long eval_cost(uint32_t *out) {
    uint32_t *cur = (uint32_t *)malloc((size_t)N * sizeof(uint32_t));
    uint32_t *nxt = (uint32_t *)malloc((size_t)N * sizeof(uint32_t));
    int full = 2 * K;
    memset(cur, 0, (size_t)N * sizeof(uint32_t));
    for (int b = 0; b < full; b++) cur[(size_t)b * G] = 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    memcpy(out, cur, (size_t)N * sizeof(uint32_t));
    long long unreached = 0;
    for (int v = 0; v < N; v++) unreached += full - popc(cur[v]);
    long long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1][i] == lay[l2][i] && Sv[l1][i] == Sv[l2][i]) dup++;
    free(cur);
    free(nxt);
    return unreached + (long long)PEN * dup;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i]; lay[l][i] = lay[l][j]; lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) Sv[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static void print_graph(void) {
    int E = K * G * d;
    printf("%d %d\n", N, E);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    limit_ms = atoll(argv[8]);
    t0 = clock();
    if (d < 1 || d > MAXD || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 > MAXK2 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    if (R < 0) R += M;
    G = M * K2;
    N = 2 * K * G;
    long long p = 1 % M;
    for (int b = 0; b < K2; b++) {
        pw[b] = (int)p;
        p = (p * R) % M;
    }
    if (p != 1 % M) { printf("0 0\n"); return 0; }

    invT = (int *)malloc((size_t)G * sizeof(int));
    nbr = (int *)malloc((size_t)d * N * sizeof(int));
    curR = (uint32_t *)malloc((size_t)N * sizeof(uint32_t));
    trialR = (uint32_t *)malloc((size_t)N * sizeof(uint32_t));
    if (!invT || !nbr || !curR || !trialR) { printf("0 0\n"); return 0; }

    for (int s = 0; s < G; s++) {
        int found = -1;
        for (int t = 0; t < G; t++)
            if (gmul(s, t) == 0) { found = t; break; }
        if (found < 0) { printf("0 0\n"); return 0; }
        invT[s] = found;
    }

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x123456789ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    const long long ITERS = 6000, PATIENCE = 1500;
    uint32_t fm = (uint32_t)((1ull << (2 * K)) - 1ull);

    while (elapsed_ms() < limit_ms) {
        random_init();
        long long cost = eval_cost(curR);
        double c0 = cost > 0 ? (double)cost : 1.0;
        long long best = cost, last = 0;

        for (long long it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 31) == 0 && elapsed_ms() >= limit_ms) break;
            if (it - last > PATIENCE) break;
            double temp = 0.01 * c0 * (1.0 - (double)it / (double)ITERS);
            if (temp < 0.5) temp = 0.5;

            if (K >= 2 && rndint(1000) < 250) {
                int l = rndint(d);
                int i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                set_dart(l, i1);
                set_dart(l, i2);
                long long c2 = eval_cost(trialR);
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                    memcpy(curR, trialR, (size_t)N * sizeof(uint32_t));
                    if (cost < best) { best = cost; last = it; }
                } else {
                    t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
                    set_dart(l, i1);
                    set_dart(l, i2);
                }
                continue;
            }

            int l = -1, i = -1;
            if (rndint(100) < 40) {
                int nbad = 0;
                for (int v = 0; v < N; v++) if (curR[v] != fm) nbad++;
                if (nbad > 0) {
                    int pick = rndint(nbad), u = -1;
                    for (int v = 0; v < N; v++) {
                        if (curR[v] != fm) {
                            if (pick == 0) { u = v; break; }
                            pick--;
                        }
                    }
                    int blk = u / G;
                    int ll = rndint(d);
                    if (blk < K) {
                        l = ll;
                        i = blk;
                    } else {
                        int jj = blk - K;
                        for (int q = 0; q < K; q++)
                            if (lay[ll][q] == jj) { l = ll; i = q; break; }
                    }
                }
            }
            if (l < 0 || i < 0) { l = rndint(d); i = rndint(K); }

            int old = Sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            Sv[l][i] = nw;
            set_dart(l, i);
            long long c2 = eval_cost(trialR);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(curR, trialR, (size_t)N * sizeof(uint32_t));
                if (cost < best) { best = cost; last = it; }
            } else {
                Sv[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost == 0) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Search driver: Python chooses group orders and base sizes; C does annealing.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_SLICE_S = 5.0


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _c_search(d, D, k, m, k2, r, seed, slice_ms):
    """Run the C annealer for one group; return (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, slice_ms],
                    stdin_graph=None, timeout=slice_ms / 1000.0 + 4.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Exact constructions: return immediately (calibration-style cases).
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

    # Main C-driven search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    if d >= 3 and D >= 3:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.5:
                break
            k = pick_k()
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best_n:
                continue
            slice_s = min(_SLICE_S, remaining - 0.5)
            if slice_s < 1.0:
                break
            trials[k] += 1
            try:
                res = _c_search(d, D, k, m, k2, r, rng.randrange(1, 2 ** 31), int(slice_s * 1000))
            except RuntimeError:
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
