"""Bi-Cayley voltage-lift search with an exact C annealer, for the weakest parent case.

Change from the parent: the lift search is moved into C. For a bi-Cayley lift over a
semidirect product Z_m x| Z_k2 with k base vertices per side, distances from every vertex
are translates of distances from the 2k block representatives, so validity needs only 2k
BFS runs per evaluation. The annealer repairs voltages and layer permutations until every
representative reaches every vertex within D, so each returned lift is exactly valid.
Python keeps K_{d,d} as the fallback, runs exact constructions for D = 3, 4, and checks
every accepted graph with lib.is_valid.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealer.
 * Usage: prog d D K M K2 R seed time_limit
 * Group: Z_M x| Z_K2, element (a,b) coded as a*K2+b, (a,b)*(c,e) = (a + R^b c, b+e).
 * Base: K A-blocks and K B-blocks. Layer l pairs A-block i with B-block P[l][i] (a
 * permutation per layer) with voltage V[l][i]: A_{i,g} ~ B_{P,g*V}.
 * Every layer is a perfect matching between blocks, so the graph is d-regular and bipartite.
 * Cost = unreached (source, vertex) pairs over the 2K block representatives + 20 * duplicate
 * edges. Cost 0 means the lift is valid.
 * stdout: "n m" + edges of the first valid lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXL 64
#define MAXK 8
#define MAXN 131072
#define MAXK2 4096
#define PATIENCE 4000

static int d, D, K, M, K2, R, G, N;
static long long pw[MAXK2];
static int P[MAXL][MAXK];
static int IP[MAXL][MAXK];
static int V[MAXL][MAXK];
static int vis[MAXN];
static int qu[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int mulg(int x, int y) {
    long long a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (a + pw[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int invg(int x) {
    long long a = x / K2, b = x % K2;
    long long nb = (K2 - b) % K2;
    long long t = (M - (pw[nb] * a) % M) % M;
    return (int)(t * K2 + nb);
}

/* Neighbour of vertex v in layer l. */
static int nbr(int v, int l) {
    int blk = v / G;
    int h = v - blk * G;
    if (blk < K) {
        int p = P[l][blk];
        return (K + p) * G + mulg(h, V[l][blk]);
    } else {
        int j = blk - K;
        int i = IP[l][j];
        return i * G + mulg(h, invg(V[l][i]));
    }
}

static long dups(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (P[l][i] == P[l2][i] && V[l][i] == V[l2][i]) c++;
    return c;
}

static long full_cost(void) {
    long cost = 0;
    for (int b = 0; b < 2 * K; b++) {
        int src = b * G;
        int head = 0, tail = 0;
        stamp++;
        qu[tail++] = src;
        vis[src] = stamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = qu[head++];
                for (int l = 0; l < d; l++) {
                    int w = nbr(v, l);
                    if (vis[w] != stamp) {
                        vis[w] = stamp;
                        qu[tail++] = w;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost + 20L * dups();
}

static void randomize(void) {
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            P[l][i] = perm[i];
            IP[l][perm[i]] = i;
            V[l][i] = rndint(G);
        }
    }
}

/* Simulated annealing with restarts. Returns 1 when P, V hold a zero-cost lift. */
static int anneal(double deadline) {
    while (now() < deadline) {
        randomize();
        long cost = full_cost();
        if (cost == 0) return 1;
        double T0 = cost * 0.05 > 1.0 ? cost * 0.05 : 1.0;
        double T = T0;
        long best = cost, since = 0;
        while (1) {
            if (now() >= deadline) return 0;
            int typ = rndint(4);
            if (typ < 3 || K == 1) {
                int l = rndint(d), i = rndint(K);
                int old = V[l][i];
                int nv = rndint(G);
                if (nv == old) continue;
                V[l][i] = nv;
                long nc = full_cost();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                    cost = nc;
                } else {
                    V[l][i] = old;
                }
            } else {
                int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
                if (i1 == i2) continue;
                int a = P[l][i1], b = P[l][i2];
                P[l][i1] = b;
                P[l][i2] = a;
                IP[l][b] = i1;
                IP[l][a] = i2;
                long nc = full_cost();
                if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                    cost = nc;
                } else {
                    P[l][i1] = a;
                    P[l][i2] = b;
                    IP[l][a] = i1;
                    IP[l][b] = i2;
                }
            }
            if (cost == 0) return 1;
            if (cost < best) {
                best = cost;
                since = 0;
            } else if (++since > PATIENCE) {
                break;
            }
            T *= 0.9995;
            if (T < 0.3) T = T0;
        }
    }
    return 0;
}

static void print_graph(void) {
    long m = (long)d * K * G;
    printf("%d %ld\n", N, m);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++)
            for (int l = 0; l < d; l++) {
                int u = i * G + g;
                int w = (K + P[l][i]) * G + mulg(g, V[l][i]);
                printf("%d %d\n", u, w);
            }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    K = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    long seed = atol(argv[7]);
    double limit = atof(argv[8]);
    if (d < 1 || d > MAXL || D < 1 || K < 1 || K > MAXK || M < 1 || K2 < 1 || K2 > MAXK2) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if ((long)2 * K * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * K * G;
    R %= M;
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (pw[b - 1] * R) % M;
    if ((pw[K2 - 1] * R) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double deadline = t0 + limit * 0.9 - 0.1;
    if (anneal(deadline)) print_graph();
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent).
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


def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices of opposite sides."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    """Saturate, but return the input unchanged if anything fails or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# Group sampling and C runner.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_K2_CHOICES = (1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16)
_SLICE = 5.0


def _sample_group(target, rng):
    """Return (m, k2, r) with G = m*k2 >= target for Z_m x| Z_k2, or None."""
    for _ in range(200):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        for _ in range(80):
            c = rng.randrange(1, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                return m, k2, c
    return None


def _run_lift(d, D, k, m, k2, r, seed, budget):
    """Run the C annealer once. Returns (n, edges); n == 0 when no lift was found."""
    text = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, round(budget, 2)],
                     stdin_graph=None, timeout=budget + 20)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(2.0, 0.88 * time_limit - 2.0)
    final = t0 + total
    rng = random.Random(seed)

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions. Calibration-style cases return immediately.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Bi-Cayley lift search in C. Goal starts at a fraction of the Moore bound and decays
    # on failure, jumping up on success.
    moore = lib.moore_bound(d, D)
    lift_deadline = final - 3.0
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    goal = max(best_n * 1.05, 0.35 * moore)
    attempt = 0
    val_time = 0.0

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = lift_deadline - time.monotonic() - val_time
        if remaining < 2.0:
            break
        k = pick_k()
        target = max(2, math.ceil(goal / (2 * k)))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.02, goal * 0.85)
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G > moore:
            goal = max(best_n * 1.02, goal * 0.85)
            continue
        if 2 * k * G <= best_n:
            goal = max(goal, best_n * 1.03)
            continue

        trials[k] += 1
        attempt += 1
        budget = min(_SLICE, remaining)
        try:
            n, e = _run_lift(d, D, k, m, k2, r, seed * 1000 + attempt, budget)
        except Exception:
            n, e = 0, []

        if n > 0:
            tv = time.monotonic()
            ok = consider(n, e)
            val_time = max(val_time, time.monotonic() - tv)
            if ok:
                wins[k] += 1
                goal = max(goal, best_n * 1.03)
                continue
        goal = max(best_n * 1.02, goal * 0.85)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
