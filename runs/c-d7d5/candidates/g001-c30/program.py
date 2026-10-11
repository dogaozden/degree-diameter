"""Bi-Cayley lift search for bipartite graphs with max degree d and diameter D.

Each candidate is a lift of a d-regular bipartite base on K + K vertices over a
semidirect product Z_m x| Z_k2. The C engine runs simulated annealing on two
move types: voltage changes, and a new target-swap move that permutes the
endpoints of two darts within one layer. It keeps every vertex at degree d.
Python sweeps group orders just above the best size found so far.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DUP_PEN 100000LL
#define ITERS 40000LL

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec;
}

static int d, D, K, G, N;
static int *MT;        /* G x G multiplication table of Z_m x|_r Z_k2 */
static int *P;         /* P[l*K+i]: base vertex on the B side hit by A_i in layer l */
static int *V;         /* V[l*K+i]: voltage (group element) of that dart */
static int *adj;       /* N*d neighbour slots, exactly d per vertex */
static int *stamp;
static int *queue_buf;
static int curstamp = 0;

/* Element (a,b) is coded a*k2+b; (a,b)*(c,e) = (a + r^b c, b + e). */
static void build_group(int m, int k2, int r) {
    G = m * k2;
    int *pw = (int *)malloc(sizeof(int) * (size_t)k2);
    long long v = 1 % m;
    for (int b = 0; b < k2; b++) {
        pw[b] = (int)v;
        v = (v * r) % m;
    }
    MT = (int *)malloc(sizeof(int) * (size_t)G * (size_t)G);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long long aa = ((long long)a + (long long)pw[b] * c) % m;
            int bb = (b + e) % k2;
            MT[x * G + y] = (int)(aa * k2 + bb);
        }
    }
    free(pw);
}

/* A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart (l,i) joins A_{i,g} to B_{P,g*V}. */
static void build_adj(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = P[l * K + i], s = V[l * K + i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + MT[g * G + s];
                adj[a * d + l] = b;
                adj[b * d + l] = a;
            }
        }
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (P[l * K + i] == P[l2 * K + i] && V[l * K + i] == V[l2 * K + i]) c++;
    return c;
}

/* Unreached (representative, vertex) pairs. Left translation is an automorphism,
   and vertex 0 of each block is a representative of its orbit. */
static long long eval_cost(void) {
    long long unreached = 0;
    for (int rr = 0; rr < 2 * K; rr++) {
        int src = rr * G;
        curstamp++;
        int head = 0, tail = 0, lvl = 0;
        queue_buf[tail++] = src;
        stamp[src] = curstamp;
        while (head < tail && lvl < D) {
            int end = tail;
            while (head < end) {
                int u = queue_buf[head++];
                const int *au = adj + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = au[t];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        queue_buf[tail++] = v;
                    }
                }
            }
            lvl++;
        }
        unreached += N - tail;
    }
    return unreached + DUP_PEN * (long long)dup_count();
}

static long long full_cost(void) {
    build_adj();
    return eval_cost();
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        int *p = P + (size_t)l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) V[l * K + i] = rndint(G);
    }
}

static void print_graph(void) {
    int m = K * G * d;
    printf("%d %d\n", N, m);
    for (int a = 0; a < K * G; a++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", a, adj[a * d + t]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int m = atoi(argv[5]), k2 = atoi(argv[6]), r = atoi(argv[7]);
    K = atoi(argv[8]);
    if (d < 1 || D < 1 || K < 1 || m < 1 || k2 < 1 || r < 0 ||
        (long long)m * k2 > 3000 || (long long)K * m * k2 > 200000) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    build_group(m, k2, r);
    N = 2 * K * G;
    P = (int *)malloc(sizeof(int) * (size_t)d * K);
    V = (int *)malloc(sizeof(int) * (size_t)d * K);
    adj = (int *)malloc(sizeof(int) * (size_t)N * d);
    stamp = (int *)calloc((size_t)N, sizeof(int));
    queue_buf = (int *)malloc(sizeof(int) * (size_t)N);

    double deadline = now_s() + budget;
    long long cur = -1;
    int found = 0;
    while (!found && now_s() < deadline) {
        random_init();
        cur = full_cost();
        for (long long it = 0; it < ITERS && cur > 0; it++) {
            if ((it & 31) == 0 && now_s() > deadline) break;
            double T = 6.0 * pow(0.2 / 6.0, (double)it / (double)ITERS);
            int l = rndint(d);
            if (K < 2 || rndint(2) == 0) {
                int idx = l * K + rndint(K);
                int old = V[idx];
                V[idx] = rndint(G);
                long long c2 = full_cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else V[idx] = old;
            } else {
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int *p = P + (size_t)l * K;
                int t = p[i1]; p[i1] = p[i2]; p[i2] = t;
                long long c2 = full_cost();
                if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
                else { t = p[i1]; p[i1] = p[i2]; p[i2] = t; }
            }
        }
        if (cur == 0) found = 1;
    }
    if (full_cost() == 0) print_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact or structured baselines.
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
# Group sampling and the C search call.
# ----------------------------------------------------------------------------

def _group_options(G):
    """All (m, k2, r) with m * k2 == G giving a valid semidirect product Z_m x| Z_k2.

    k2 == 1 gives the cyclic group. r = 1 gives the direct product, which is included.
    """
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if k2 == 1:
            out.append((m, 1, 1 % m if m > 1 else 0))
            continue
        if m == 1:
            out.append((1, k2, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def _run_search(d, D, seed, budget, m, k2, r, K):
    """Run the C annealer for one group and base size. Returns (n, edges) or None."""
    text = lib.run_c(C_SOURCE, [d, D, seed, budget, m, k2, r, K], timeout=budget + 15.0)
    n, edges = lib.parse_graph_text(text)
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    deadline = t_start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search: ramp the target order just above the current best, with a
    # random base size K and a random group of matching order.
    if d >= 3 and D >= 2:
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                break
            best_n = best[0]
            K = rng.choice([1, 2, 2, 3, 4])
            target = best_n + 2 + rng.randrange(0, max(3, best_n // 10))
            G = -(-target // (2 * K))
            opts = _group_options(G)
            m, k2, r = rng.choice(opts)
            budget = min(remaining - 1.5, 8.0)
            if budget < 1.0:
                break
            try:
                res = _run_search(d, D, rng.randrange(1, 2 ** 31), budget, m, k2, r, K)
            except (RuntimeError, ValueError):
                break
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
