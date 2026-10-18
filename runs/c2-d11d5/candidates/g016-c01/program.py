"""Bi-Cayley lift search with a C annealer over semidirect groups Z_M x| Z_K2.

Each candidate has K base blocks per side and d layers. Layer l pairs A-block i with B-block
P[l][i] through a group voltage S[l][i]. Vertex transitivity within blocks comes from left
multiplication, so the C engine only BFSes from the 2K block representatives. Annealing
moves permutations and voltages until every representative reaches all vertices within D.
Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction)
is the fallback.
"""
import itertools
import math
import random
import time

import lib


CMAXN = 12000  # must match MAXN in C_SOURCE

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12000
#define MAXD 16
#define MAXK 8
#define PEN 1000L
#define MAXIT 60000L
#define PATIENCE 4000L

static int d, D, K, M, K2, R, G, N;
static long long powr[64];
static int P[MAXD][MAXK], PI[MAXD][MAXK], S[MAXD][MAXK];
static int adj[MAXN * MAXD];
static unsigned char VIS[2 * MAXK * MAXN];
static unsigned char VISC[2 * MAXK * MAXN];
static int queue_[MAXN];
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

/* Semidirect product Z_M x| Z_K2: element a*K2+b, (a,b)*(c,e) = (a + r^b c, b + e). */
static int mulg(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = (long long)a + powr[b] * (long long)c;
    return (int)(t % M) * K2 + (b + e) % K2;
}

static int invg(int s) {
    int a = s / K2, b = s % K2;
    int nb = (K2 - b) % K2;
    long long t = -(powr[nb] * (long long)a) % M;
    if (t < 0) t += M;
    return (int)t * K2 + nb;
}

/* Layer l: A-block i joined to B-block j with voltage s: A(i,g) ~ B(j, g*s). */
static void set_dart(int l, int i, int j, int s) {
    int is = invg(s);
    for (int g = 0; g < G; g++) {
        int A = i * G + g;
        int B = (K + j) * G + mulg(g, s);
        adj[A * d + l] = B;
    }
    for (int h = 0; h < G; h++) {
        int B = (K + j) * G + h;
        adj[B * d + l] = i * G + mulg(h, is);
    }
}

static void swap_perm(int l, int i1, int i2) {
    int t = P[l][i1];
    P[l][i1] = P[l][i2];
    P[l][i2] = t;
    PI[l][P[l][i1]] = i1;
    PI[l][P[l][i2]] = i2;
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) PI[l][P[l][i]] = i;
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i, P[l][i], S[l][i]);
}

/* Duplicate darts: same A-block, same B-block, same voltage in two layers. */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (P[l][i] == P[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Cost = total (representative, vertex) pairs beyond distance D, plus duplicate penalty. */
static long evaluate(void) {
    long cost = 0;
    int reps = 2 * K;
    for (int r = 0; r < reps; r++) {
        unsigned char *vis = VIS + (size_t)r * N;
        memset(vis, 0, (size_t)N);
        int src = r * G;
        int head = 0, tail = 1;
        queue_[0] = src;
        vis[src] = 1;
        for (int dep = 0; dep < D; dep++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int v = queue_[head++];
                const int *a = adj + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = a[l];
                    if (!vis[u]) {
                        vis[u] = 1;
                        queue_[tail++] = u;
                    }
                }
            }
        }
        cost += N - tail;
    }
    cost += PEN * (long)dup_count();
    return cost;
}

static int pick_unreached(int *out) {
    int r = rndint(2 * K);
    const unsigned char *vis = VISC + (size_t)r * N;
    int start = rndint(N);
    for (int t = 0; t < N; t++) {
        int v = start + t;
        if (v >= N) v -= N;
        if (!vis[v]) {
            *out = v;
            return 1;
        }
    }
    return 0;
}

static void print_graph(void) {
    long m = (long)K * G * d;
    printf("%d %ld\n", N, m);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, adj[u * d + l]);
}

static int anneal(double until) {
    while (now() < until) {
        random_config();
        long cost = evaluate();
        memcpy(VISC, VIS, sizeof(unsigned char) * (size_t)(2 * K) * N);
        if (cost == 0) {
            print_graph();
            return 1;
        }
        long c0 = cost, best = cost, last = 0;
        for (long it = 1; it < MAXIT; it++) {
            if ((it & 63) == 0 && now() > until) return 0;
            if (it - last > PATIENCE) break;
            double T = 0.01 * (double)c0 * (1.0 - (double)it / (double)MAXIT);
            if (T < 0.5) T = 0.5;

            if (K >= 2 && rnd01() < 0.2) {
                int l = rndint(d), i1 = rndint(K), i2 = rndint(K);
                if (i1 == i2) continue;
                swap_perm(l, i1, i2);
                set_dart(l, i1, P[l][i1], S[l][i1]);
                set_dart(l, i2, P[l][i2], S[l][i2]);
                long c2 = evaluate();
                if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                    cost = c2;
                    memcpy(VISC, VIS, sizeof(unsigned char) * (size_t)(2 * K) * N);
                    if (cost < best) { best = cost; last = it; }
                    if (cost == 0) {
                        print_graph();
                        return 1;
                    }
                } else {
                    swap_perm(l, i1, i2);
                    set_dart(l, i1, P[l][i1], S[l][i1]);
                    set_dart(l, i2, P[l][i2], S[l][i2]);
                }
            } else {
                int l, i, v;
                if (rnd01() < 0.5 && pick_unreached(&v)) {
                    int b = v / G;
                    l = rndint(d);
                    if (b < K) i = b;
                    else i = PI[l][b - K];
                } else {
                    l = rndint(d);
                    i = rndint(K);
                }
                int old = S[l][i];
                int nw = rndint(G);
                if (nw == old) continue;
                S[l][i] = nw;
                set_dart(l, i, P[l][i], nw);
                long c2 = evaluate();
                if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                    cost = c2;
                    memcpy(VISC, VIS, sizeof(unsigned char) * (size_t)(2 * K) * N);
                    if (cost < best) { best = cost; last = it; }
                    if (cost == 0) {
                        print_graph();
                        return 1;
                    }
                } else {
                    S[l][i] = old;
                    set_dart(l, i, P[l][i], old);
                }
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time_limit K M K2 R\n", argv[0]);
        return 2;
    }
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 2 || d > MAXD || D < 2 || K < 1 || K > MAXK || M < 2 || K2 < 1 || K2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    if (N < 2 || N > MAXN) {
        printf("0 0\n");
        return 0;
    }
    R %= M;
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = powr[b - 1] * R % M;
    if ((powr[K2 - 1] * R) % M != 1 % M) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double until = t0 + limit * 0.92 - 0.2;
    if (!anneal(until)) printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions.
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


# ----------------------------------------------------------------------------
# Group sampling for the C lift search.
# ----------------------------------------------------------------------------

def _pick_group(K, target, moore, rng):
    """Return (M, K2, R) with 2*K*M*K2 >= target (about), within C limits and the Moore bound, or None."""
    base = -(-target // (2 * K))
    for _ in range(60):
        K2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16])
        M = max(2, -(-(base + rng.randrange(0, 3)) // K2))
        G = M * K2
        if 2 * K * G > CMAXN or 2 * K * G > moore:
            continue
        if K2 == 1:
            return M, 1, 1
        for _ in range(200):
            c = rng.randrange(1, M)
            if math.gcd(c, M) == 1 and pow(c, K2, M) == 1 % M:
                return M, K2, c
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback
    best_n = fallback[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

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
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)
    moore = lib.moore_bound(d, D)

    # Ratchet the target order: success raises it, failure eases it back toward the best.
    goal = min(moore, max(best_n + 2, int(best_n * 1.1)))
    attempt = 0
    while True:
        remaining = final - time.monotonic()
        if remaining < 3.0:
            break
        cs = min(remaining - 1.0, max(5.0, remaining / 4.0))
        K = rng.choice([1, 2, 2, 3, 3, 4, 4, 5, 6])
        g = _pick_group(K, goal, moore, rng)
        if g is None:
            goal = max(best_n + 2, int(goal * 0.99))
            continue
        M, K2, R = g
        attempt += 1
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, seed * 1009 + attempt, round(cs, 2), K, M, K2, R],
                             timeout=cs + 10)
            n, edges = lib.parse_graph_text(text)
        except Exception:
            n, edges = 0, []
        if n > best_n and lib.is_valid(n, edges, d, D):
            best, best_n = (n, edges), n
            goal = min(moore, int(n * 1.02) + 2)
        else:
            goal = max(best_n + 2, int(goal * 0.985))

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
