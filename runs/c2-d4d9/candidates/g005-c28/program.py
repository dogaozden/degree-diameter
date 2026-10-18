"""Bipartite Cayley search for degree-diameter graphs (a new engine for this island).

Construction: take a metacyclic group G = Z_m x| Z_k of order N and d distinct connection
elements S. The bipartite graph has vertices (g,0) and (h,1) for g,h in G, with edges
(g,0)-(gs,1) for s in S. Every vertex has degree d, and the graph is bipartite by construction.
Left multiplication is an automorphism, so the diameter check needs only two BFS runs, one from
(e,0) and one from (e,1). The C engine anneals over S (and over random groups of each order) to
minimise unreached pairs, and grows N whenever a solution appears. Python supplies algebraic
fallbacks and keeps the largest graph that lib.is_valid accepts.
"""
import itertools
import time

import lib

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

static int d, D;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
typedef struct {
    int N, m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int k = G->k;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)(((long)a + (long)G->rp[b] * c) % G->m) * k + (b + e) % k;
}

static int ginv(const Grp *G, int x) {
    int k = G->k;
    int a = x / k, b = x % k;
    int nb = (k - b) % k;
    long c = (long)G->rp[nb] * a % G->m;
    c = (G->m - c) % G->m;
    return (int)(c * k + nb);
}

static void set_group(Grp *G, int m, int k, int r) {
    G->N = m * k;
    G->m = m;
    G->k = k;
    G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

/* Uniform random non-abelian metacyclic group of order N; cyclic Z_N if none exists. */
static void pick_group(int N, Grp *G) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int k = 2; k <= N / 2; k++) {
        if (N % k) continue;
        int m = N / k;
        for (int r = 2; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) { bm = N; bk = 1; br = 1; }
    set_group(G, bm, bk, br);
}

/* BFS in the bipartite Cayley graph: side 0 is index g, side 1 is index N+h.
 * (g,0) ~ (gs,1) for s in S, and (h,1) ~ (h s^-1, 0). */
static int stamp_arr[2 * MAXN];
static int queue_arr[2 * MAXN];
static int tick = 0;

static int reach_count(const Grp *G, const int *S, const int *sinv, int start) {
    int N = G->N;
    if (++tick == 0x7fffffff) {
        memset(stamp_arr, 0, sizeof stamp_arr);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp_arr[start] = tick;
    queue_arr[tail++] = start;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = queue_arr[head];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + gmul(G, v, S[i]);
                    if (stamp_arr[u] != tick) {
                        stamp_arr[u] = tick;
                        queue_arr[tail++] = u;
                    }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = gmul(G, h, sinv[i]);
                    if (stamp_arr[u] != tick) {
                        stamp_arr[u] = tick;
                        queue_arr[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the two representative vertices (e,0) and (e,1). Zero means valid. */
static long eval(const Grp *G, const int *S) {
    int N = G->N;
    int sinv[MAXD];
    for (int i = 0; i < d; i++) sinv[i] = ginv(G, S[i]);
    long bad = 2L * N - reach_count(G, S, sinv, 0);
    bad += 2L * N - reach_count(G, S, sinv, N);
    return bad;
}

/* Simulated annealing over the d connection elements of G. */
static int anneal(const Grp *G, int *S, double until, long maxsteps) {
    int N = G->N;
    if (N < d) return 0;
    for (int i = 0; i < d; i++) {
        int t, clash;
        do {
            t = rndint(N);
            clash = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == t) clash = 1;
        } while (clash);
        S[i] = t;
    }
    long bad = eval(G, S);
    double T0 = 1.5;
    for (long s = 0; s < maxsteps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) return 0;
        double T = T0 * (1.0 - (double)s / (double)maxsteps) + 0.02;
        int i = rndint(d), t = rndint(N);
        int clash = 0;
        for (int j = 0; j < d; j++)
            if (S[j] == t) { clash = 1; break; }
        if (clash) continue;
        int old = S[i];
        S[i] = t;
        long nb = eval(G, S);
        long df = nb - bad;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) bad = nb;
        else S[i] = old;
    }
    return bad == 0;
}

static Grp bestG;
static int bestS[MAXD];
static int bestN = 0;

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    int N = d + 1;
    if (N < 6) N = 6;
    int fails = 0;
    static Grp G;
    int S[MAXD];
    while (now() < t_end) {
        if (N > MAXN / 2) break;
        pick_group(N, &G);
        double remain = t_end - now();
        double slice = remain / 10.0;
        if (slice < 0.3) slice = 0.3;
        if (slice > 4.0) slice = 4.0;
        if (slice > remain) slice = remain;
        if (anneal(&G, S, now() + slice, 30000)) {
            bestN = N;
            bestG = G;
            memcpy(bestS, S, sizeof(int) * d);
            fails = 0;
            int step = N / 32;
            if (step < 1) step = 1;
            N += step;
        } else {
            fails++;
            if (bestN > 0) {
                if (fails >= 3 && N - bestN > 1) {
                    N = bestN + (N - bestN) / 2;
                    fails = 0;
                }
            } else if (fails >= 3) {
                N = N * 9 / 10;
                if (N < d + 1) N = d + 1;
                fails = 0;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    long M = (long)bestN * d;
    printf("%d %ld\n", 2 * bestN, M);
    for (int g = 0; g < bestN; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, bestN + gmul(&bestG, g, bestS[i]));
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (filtered by lib.is_valid by the caller)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
    return [c for c in out if c is not None]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
