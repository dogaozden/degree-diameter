import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley search over semidirect products Z_M x| Z_K2.
#
# Group elements are coded as a*K2 + b with (a,b)(c,e) = (a + r^b c, b + e).
# Vertices: A_g = g and B_h = G + h, with G = M*K2. Connection set S of d
# distinct group elements gives edges A_g -- B_{g*s} for s in S, so the graph
# is d-regular and bipartite on 2G vertices. The group acts on the graph by
# left multiplication and is transitive on each side, so the diameter is at
# most D iff BFS from A_e and from B_e reaches everything within D steps.
# Simulated annealing over S minimises the number of unreached pairs.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 4096
#define MAXD 64
#define ITERS 40000

static int d, D, M, K2, R, G, N;
static long long pw[64];
static int S[MAXD];
static int *adj, *deg, *vis, *que;
static int stamp = 0;
static uint64_t rs;

static uint64_t nxt(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(nxt() % (uint64_t)n);
}

static double urand(void) {
    return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0);
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long na = ((long long)a + pw[b] * (long long)c) % M;
    int nb = (b + e) % K2;
    return (int)na * K2 + nb;
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static void random_S(void) {
    for (int t = 0; t < d; t++) {
        int x;
        do {
            x = rndint(G);
        } while (in_S(x, t));
        S[t] = x;
    }
}

static void build_adj(void) {
    for (int i = 0; i < N; i++) deg[i] = 0;
    for (int g = 0; g < G; g++) {
        for (int t = 0; t < d; t++) {
            int a = g;
            int b = G + gmul(g, S[t]);
            if (deg[a] < d && deg[b] < d) {
                adj[a * d + deg[a]++] = b;
                adj[b * d + deg[b]++] = a;
            }
        }
    }
}

static long long cost(void) {
    build_adj();
    long long total = 0;
    int reps[2];
    reps[0] = 0;
    reps[1] = G;
    for (int r = 0; r < 2; r++) {
        int src = reps[r];
        stamp++;
        int head = 0, tail = 0;
        vis[src] = stamp;
        que[tail++] = src;
        for (int lvl = 0; lvl < D && head < tail; lvl++) {
            int end = tail;
            while (head < end) {
                int u = que[head++];
                for (int k = 0; k < d; k++) {
                    int v = adj[u * d + k];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        que[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void output_graph(void) {
    printf("%d %d\n", N, G * d);
    for (int g = 0; g < G; g++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", g, G + gmul(g, S[t]));
}

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    M = atoi(argv[3]);
    K2 = atoi(argv[4]);
    R = atoi(argv[5]);
    double secs = atof(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);

    if (d < 1 || d > MAXD || D < 1 || M < 1 || K2 < 1 || K2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G > MAXG || G < d) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * G;

    R = R % M;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++)
        pw[b] = ((long long)pw[b - 1] * R) % M;

    adj = (int *)calloc((size_t)N * (size_t)d, sizeof(int));
    deg = (int *)calloc((size_t)N, sizeof(int));
    vis = (int *)calloc((size_t)N, sizeof(int));
    que = (int *)calloc((size_t)N, sizeof(int));
    if (!adj || !deg || !vis || !que) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
#define ELAPSED ((double)(clock() - t0) / CLOCKS_PER_SEC)

    while (ELAPSED < secs) {
        random_S();
        long long cur = cost();
        for (int it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 63) == 0 && ELAPSED >= secs) break;
            int t = rndint(d);
            int old = S[t];
            int nw = rndint(G);
            if (in_S(nw, d)) continue;
            S[t] = nw;
            long long c2 = cost();
            double temp = 3.0 * (1.0 - (double)it / ITERS) + 0.1;
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / temp)) {
                cur = c2;
            } else {
                S[t] = old;
            }
        }
        if (cur == 0) {
            output_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact or safe constructions used as fallbacks and calibration answers.
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
# Group sampling for the C search: returns (M, K2, R) describing Z_M x| Z_K2
# with R^K2 = 1 mod M, of total order G.
# ----------------------------------------------------------------------------

def _group_for_order(G, rng):
    """Return a random (M, K2, R) with M * K2 == G, or the cyclic group if nothing else fits."""
    divs = [k for k in range(1, min(G, 40) + 1) if G % k == 0]
    rng.shuffle(divs)
    for K2 in divs:
        M = G // K2
        if M == 1:
            return (1, K2, 0)
        if K2 == 1:
            return (M, 1, 0)
        cands = [r for r in range(1, M)
                 if math.gcd(r, M) == 1 and pow(r, K2, M) == 1 % M]
        if cands:
            return (M, K2, rng.choice(cands))
    return (G, 1, 0)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t_start + budget
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

    # Exact constructions. These return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                al = lib.araujo_lopez_graph(d - 2)
                consider(al[0], al[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley graphs over semidirect products, with a ladder on
    # the group order G (the graph has 2G vertices). Climb while the C search
    # succeeds; on repeated failure, shrink the step and retry fresh groups.
    try:
        best_G = max(d, best_n // 2)
        step = 1
        fails = 0
        max_order = lib.moore_bound(d, D)
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            G = best_G + step
            if G > 4000 or 2 * G > max_order:
                if step > 1:
                    step = max(1, step // 2)
                    continue
                break
            M, K2, R = _group_for_order(G, rng)
            slice_s = min(remaining - 0.5, 3.0)
            if slice_s < 0.5:
                break
            seed_c = rng.randrange(1, 1 << 30)
            try:
                out = lib.run_c(C_SOURCE, [d, D, M, K2, R, f"{slice_s:.2f}", seed_c],
                                timeout=slice_s + 10.0)
                n, e = lib.parse_graph_text(out)
            except RuntimeError:
                break
            except ValueError:
                n, e = 0, []
            if n > 0 and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_G = max(best_G, G)
                step = min(step * 2, max(1, best_G // 16))
                fails = 0
            else:
                fails += 1
                if fails >= 2:
                    step = max(1, step // 2)
                    fails = 0
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
