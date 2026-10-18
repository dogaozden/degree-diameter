"""Non-abelian group-table lifts for the bipartite degree-diameter problem.

Construction: pick a finite group G of order N (semidirect products Z_m x|_r Z_k,
with r^k = 1 mod m, plus the cyclic case) and B in {2, 3, 4} orbits per side. Dart
slot t of left orbit i sends L(i,g) to R(sigma_t(i), g*v). Each slot uses a random
permutation sigma_t, so the base is d-regular and every d-regular bipartite base
on B+B vertices is covered (Koenig). Left translations are automorphisms, so BFS
from the 2B orbit representatives decides the diameter.

The group multiplication table is passed to the C engine on stdin as "N*N" pairs
(index, product), so the C code needs no field or group arithmetic of its own.
The C engine runs simulated annealing over voltages to drive the uncovered count
to zero, checks simplicity, and checks all pairs when the graph has at most 5000
vertices. Python re-checks every result with lib.is_valid and keeps a valid
fallback (K_{d,d}, or a projective-plane / Araujo-Lopez / quadrangle graph when it
applies).
"""
import itertools
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Group-table multi-orbit lifts. Usage: prog d D seed time_limit B
 * stdin: "N N*N" then N*N pairs "idx prod" giving the multiplication table
 * (identity must be element 0). Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXB 4
#define MAXD 32
#define MAXV (2 * MAXB * MAXN)

static int d, D, B, N, BN, V;
static int *MUL, *INV;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static int adjv[MAXV][MAXD];

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

static int base_connected(void) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) { seenL[i] = 0; seenR[i] = 0; }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(void) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static void random_pattern(void) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected() && set_incidence()) break;
    }
}

/* Darts of the same (i, target) need distinct voltages; only slots t2 < limit are checked. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(void) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

/* BFS to depth D from src; returns the number of vertices reached. */
static int bfs_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + MUL[g * N + vol[i][t]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + MUL[x * N + INV[vol[i][t]]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Total number of (representative, vertex) pairs not yet within distance D. */
static long cover_cost(void) {
    long cost = 0;
    for (int i = 0; i < B; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < B; j++) cost += (long)(V - bfs_count((B + j) * N));
    return cost;
}

/* Restarts with random base patterns plus annealing over voltages. */
static int search(double until) {
    const int iters = 20000;
    while (now() < until) {
        random_pattern();
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                vol[i][t] = x;
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            vol[i][t] = x;
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                vol[i][t] = old;
            }
        }
        if (cost == 0 && simple_state()) return 1;
    }
    return 0;
}

static void fail(void) {
    printf("0 0\n");
    exit(0);
}

int main(int argc, char **argv) {
    if (argc < 6) fail();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    B = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3 || B < 1 || B > MAXB) fail();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) fail();
    if (n < 2 || n > MAXN || m != n * n) fail();
    N = n;
    MUL = malloc(sizeof(int) * (size_t)N * (size_t)N);
    INV = malloc(sizeof(int) * (size_t)N);
    if (!MUL || !INV) fail();
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) fail();
        if (u < 0 || u >= N * N || v < 0 || v >= N) fail();
        MUL[u] = v;
    }
    /* Identity must be element 0. */
    for (int y = 0; y < N; y++)
        if (MUL[y] != y) fail();
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) fail();
    }

    BN = B * N;
    V = 2 * BN;
    if (V > MAXV) fail();

    if (!search(t_end)) fail();
    if (!set_incidence()) fail();

    /* Build adjacency: left vertex v = i*N+g, right vertex BN + j*N + x. */
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++)
            adjv[v][t] = BN + tgt[i][t] * N + MUL[g * N + vol[i][t]];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adjv[w][k] = i * N + MUL[x * N + INV[vol[i][t]]];
        }
    }

    /* Simplicity: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adjv[v][k] == adjv[v][l]) fail();

    /* Full distance check from every vertex when cheap. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adjv[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) fail();
        }
    }

    printf("%d %d\n", V, BN * d);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adjv[v][t]);
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _semidirect_options(N):
    """All (m, k, r) with m*k = N, k >= 2, r != 1, gcd(r, m) = 1 and r^k = 1 mod m."""
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b, identity 0."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    na = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    nb = (b[:, None] + b[None, :]) % k
    return na * k + nb


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    if d >= 3 and D >= 3:
        try:
            mb = lib.moore_bound(d, D)
            # Aim above the strongest known level; windows then climb in N.
            target = max(best[0] + 1, int(0.27 * mb))
            rng = random.Random(seed * 1000003 + d * 101 + D)

            lanes = []
            for B in (4, 3, 2):
                lo = max(target // (2 * B) + 1, 2 * d)
                hi = min(mb // (2 * B), 2048)
                ns = []
                N = lo
                while N <= hi and len(ns) < 7:
                    if _semidirect_options(N):
                        ns.append(N)
                    N += 1
                lanes.append((B, ns))

            order = []
            for j in range(7):
                for B, ns in lanes:
                    if j < len(ns):
                        order.append((B, ns[j]))

            deadline = t0 + 0.85 * time_limit - 2.0
            for idx, (B, N) in enumerate(order):
                remaining = deadline - time.monotonic()
                if remaining < 6.0:
                    break
                slice_ = min(remaining - 2.0, max(6.0, remaining / 4.0))
                m, k, r = rng.choice(_semidirect_options(N))
                table = _mul_table(m, k, r)
                edges = list(enumerate(table.ravel().tolist()))
                try:
                    text = lib.run_c(C_SOURCE, [d, D, seed + idx, round(slice_, 2), B],
                                     stdin_graph=(N, edges), timeout=slice_ + 10.0)
                    consider(lib.parse_graph_text(text))
                except Exception:
                    continue
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
