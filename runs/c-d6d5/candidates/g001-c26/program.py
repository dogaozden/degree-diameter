import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltages of a lift over the semidirect
# product Z_m x| Z_k2 (element code a*k2+b), with K base vertices per side.
#
# Vertices: A_i,g = i*G + g and B_j,h = (K+j)*G + h, with G = m*k2.
# Layer l is a permutation p_l of the K base indices; dart t = l*K + i joins
# A_i,g to B_{p_l(i),g*s_t} for all g. Every vertex then has degree d.
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2K block representatives reaches every vertex.
# Cost = total unreached (representative, vertex) pairs; 0 means valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXG 2048
#define MAXK 4
#define MAXT 256
#define BIG 1000000000
#define ITERS 300000

typedef unsigned long long u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (u64)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int dd, DIAM, K, G, m, k2, rr, N, T;
static int *mul;
static int src[MAXT], tgt[MAXT], vol[MAXT], btgt[MAXT], bvol[MAXT];
static int *adj, *deg, *queue;
static unsigned *vis;
static unsigned stamp = 0;
static double budget;
static clock_t t0;

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static void build_group(void) {
    G = m * k2;
    int *pw = malloc(sizeof(int) * k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * rr) % m);
    mul = malloc(sizeof(int) * G * G);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long long aa = (a + (long long)pw[b] * c) % m;
            mul[x * G + y] = (int)(aa * k2 + (b + e) % k2);
        }
    }
    free(pw);
}

static int eval(void) {
    for (int a = 0; a < T; a++)
        for (int b = a + 1; b < T; b++)
            if (src[a] == src[b] && tgt[a] == tgt[b] && vol[a] == vol[b]) return BIG;
    N = 2 * K * G;
    memset(deg, 0, sizeof(int) * N);
    for (int t = 0; t < T; t++) {
        int i = src[t], j = tgt[t], s = vol[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + mul[g * G + s];
            adj[a * dd + deg[a]++] = b;
            adj[b * dd + deg[b]++] = a;
        }
    }
    int total = 0;
    for (int rb = 0; rb < 2 * K; rb++) {
        stamp++;
        int s0 = rb * G;
        int head = 0, tail = 1;
        queue[0] = s0;
        vis[s0] = stamp;
        for (int lev = 0; lev < DIAM; lev++) {
            int end = tail;
            if (head == end) break;
            for (; head < end; head++) {
                int u = queue[head];
                for (int q = 0; q < dd; q++) {
                    int v = adj[u * dd + q];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void randomize(void) {
    for (int l = 0; l < dd; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            int t = l * K + i;
            src[t] = i;
            tgt[t] = perm[i];
            vol[t] = rndint(G);
        }
    }
}

static void mutate(void) {
    if (K > 1 && rnd01() < 0.25) {
        int l = rndint(dd);
        int a = rndint(K), b = rndint(K);
        if (a == b) return;
        int x = l * K + a, y = l * K + b;
        int tmp = tgt[x]; tgt[x] = tgt[y]; tgt[y] = tmp;
    } else {
        int t = rndint(T);
        vol[t] = rndint(G);
    }
}

static void output(void) {
    printf("%d %d\n", 2 * K * G, T * G);
    for (int t = 0; t < T; t++) {
        int i = src[t], j = tgt[t], s = vol[t];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + mul[g * G + s];
            printf("%d %d\n", a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    K = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    rr = atoi(argv[8]);
    if (dd < 1 || DIAM < 1 || K < 1 || K > MAXK || m < 2 || k2 < 1 ||
        m * k2 > MAXG || dd * K > MAXT || rr < 1) {
        printf("0 0\n");
        return 0;
    }
    rr %= m;
    {
        long long p = 1 % m;
        for (int i = 0; i < k2; i++) p = (p * rr) % m;
        if (p != 1 % m) { printf("0 0\n"); return 0; }
    }
    build_group();
    T = dd * K;
    int cap = 2 * K * G;
    adj = malloc(sizeof(int) * cap * dd);
    deg = malloc(sizeof(int) * cap);
    queue = malloc(sizeof(int) * cap);
    vis = calloc(cap, sizeof(unsigned));

    rs ^= seed * 2654435761ULL + 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    t0 = clock();
    while (elapsed() < budget) {
        randomize();
        int cost = eval();
        for (int it = 0; it < ITERS && cost != 0; it++) {
            if ((it & 255) == 0 && elapsed() > budget) break;
            double Temp = 2.0 * (1.0 - (double)it / ITERS) + 0.05;
            memcpy(btgt, tgt, sizeof(int) * T);
            memcpy(bvol, vol, sizeof(int) * T);
            mutate();
            int c2 = eval();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / Temp)) {
                cost = c2;
            } else {
                memcpy(tgt, btgt, sizeof(int) * T);
                memcpy(vol, bvol, sizeof(int) * T);
            }
        }
        if (cost == 0) {
            output();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and glue.
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


def _semidirect_params(G):
    """All (m, k2, r) with m * k2 = G giving a valid semidirect product Z_m x| Z_k2."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Ratchet: each successful C run raises best_n, and the next run targets
    # a slightly larger group order than the current best lift.
    attempt = 0
    while D >= 3 and best_n < bound and time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        budget = min(4.0, remaining)
        if budget < 0.5:
            break
        k = rng.choice([1, 1, 1, 2])
        lo = best_n // (2 * k) + 1
        G = lo + rng.randrange(0, max(2, lo // 12))
        configs = _semidirect_params(G)
        if not configs:
            continue
        m, k2, r = rng.choice(configs)
        attempt += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, seed * 1000 + attempt, f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            continue
        if n > 0:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
