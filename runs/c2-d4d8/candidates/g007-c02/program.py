"""Bi-Cayley generator-set search over mixed groups, targeting record orders and above.

Construction: vertices A = G x {0} and B = G x {1} for a finite group G of order N. Edges
(g,0)-(g*s,1) for a d-set S of non-identity elements. Left multiplication is an automorphism that is
regular on each side, so diameter <= D holds iff BFS from A(1) and B(1) reaches everything within D.

Groups are drawn from Z_m x|_r Z_k x Z_e (metacyclic times a cyclic direct factor), a family the
voltage engine did not use. The C engine anneals S with a count of unreached pairs as its cost, and
starts at order ceil(record/2) so it aims to reproduce the record before growing past it.
Python builds algebraic starts, runs C, and accepts only a larger graph that lib.is_valid confirms.
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

#define MAXN 8192
#define MAXD 32
#define MAXG 2600
#define ANNEAL_IT 12000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

typedef struct {
    int N, m, k, e, r;
    int rp[MAXG];
} Grp;

static int d, D;
static long MOORE;
static long target_n = 0;
static double t_end;
static Graph best;
static Graph cand;

static uint16_t MT[MAXG * MAXG];
static int INV[MAXG];
static int Sg[MAXD], Sinv[MAXD];
static int distv[2 * MAXG];
static int qbuf[2 * MAXG];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

/* Group Z_m x|_r Z_k x Z_e; element index = (a*k + b)*e + c, identity 0. */
static int gmul(const Grp *G, int x, int y) {
    int ke = G->k * G->e;
    int a = x / ke, rem = x % ke, b = rem / G->e, c = rem % G->e;
    int a2 = y / ke, rem2 = y % ke, b2 = rem2 / G->e, c2 = rem2 % G->e;
    int ra = (int)(((long)a + (long)G->rp[b] * a2) % G->m);
    int rb = (b + b2) % G->k;
    int rc = (c + c2) % G->e;
    return (ra * G->k + rb) * G->e + rc;
}

static int ginv(const Grp *G, int x) {
    int ke = G->k * G->e;
    int a = x / ke, rem = x % ke, b = rem / G->e, c = rem % G->e;
    int nb = (G->k - b) % G->k;
    long t = (long)G->rp[nb] * a % G->m;
    int na = (int)((G->m - t) % G->m);
    int nc = (G->e - c) % G->e;
    return (na * G->k + nb) * G->e + nc;
}

static int divisors(int x, int *out) {
    int c = 0;
    for (int i = 1; i <= x; i++)
        if (x % i == 0) out[c++] = i;
    return c;
}

static int pick_group(int N, Grp *G) {
    static int dv1[MAXG], dv2[MAXG];
    for (int tries = 0; tries < 100; tries++) {
        int nd = divisors(N, dv1);
        int e = dv1[rndint(nd)];
        int M = N / e;
        int nm = divisors(M, dv2);
        int m = dv2[rndint(nm)];
        int k = M / m;
        G->N = N; G->m = m; G->k = k; G->e = e; G->r = 0;
        if (m == 1) {
            for (int b = 0; b < k; b++) G->rp[b] = 0;
            return 1;
        }
        for (int t = 0; t < 60; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) == 1 && powmod(r, k, m) == 1) {
                G->r = r;
                G->rp[0] = 1 % m;
                for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
                return 1;
            }
        }
    }
    return 0;
}

static void build_tables(const Grp *G) {
    int N = G->N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MT[x * N + y] = (uint16_t)gmul(G, x, y);
    for (int x = 0; x < N; x++) INV[x] = ginv(G, x);
}

static int in_set(int g, int upto) {
    for (int j = 0; j < upto; j++)
        if (Sg[j] == g) return 1;
    return 0;
}

/* Sum over the two sources A(1) and B(1) of vertices not reached within D. Zero iff diameter <= D. */
static long cost_of(int N) {
    long bad = 0;
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) distv[v] = -1;
        int head = 0, tail = 0;
        distv[s0] = 0;
        qbuf[tail++] = s0;
        while (head < tail) {
            int v = qbuf[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + MT[v * N + Sg[i]];
                    if (distv[u] < 0) { distv[u] = dv + 1; qbuf[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = MT[h * N + Sinv[i]];
                    if (distv[u] < 0) { distv[u] = dv + 1; qbuf[tail++] = u; }
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

static int attempt(int N, double until) {
    static Grp G;
    if (N - 1 < d || N > MAXG) return 0;
    if (!pick_group(N, &G)) return 0;
    build_tables(&G);
    for (int i = 0; i < d; i++) {
        int g;
        do { g = 1 + rndint(N - 1); } while (in_set(g, i));
        Sg[i] = g;
        Sinv[i] = INV[g];
    }
    long cost = cost_of(N);
    for (int it = 0; it < ANNEAL_IT && cost > 0; it++) {
        if ((it & 31) == 0 && now() > until) break;
        double T = 0.3 + 2.0 * (1.0 - (double)it / ANNEAL_IT);
        int i = rndint(d);
        int old = Sg[i], oldinv = Sinv[i];
        int g;
        do { g = 1 + rndint(N - 1); } while (in_set(g, d));
        Sg[i] = g;
        Sinv[i] = INV[g];
        long c2 = cost_of(N);
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
            cost = c2;
        } else {
            Sg[i] = old;
            Sinv[i] = oldinv;
        }
    }
    if (cost != 0) return 0;

    int V = 2 * N;
    if (V <= best.n) return 0;
    cand.n = V;
    for (int v = 0; v < V; v++) cand.deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(&cand, x, N + MT[x * N + Sg[i]]);
    best = cand;
    return 1;
}

static void search(double until) {
    int span = 1;
    for (;;) {
        double left = until - now();
        if (left <= 0.05) break;
        long lo = best.n / 2 + 1;
        if (target_n > 0) {
            long t2 = (target_n + 1) / 2;
            if (t2 > lo) lo = t2;
        }
        if (lo < d + 1) lo = d + 1;
        long N = lo + rndint(span);
        if (2 * N > MOORE || N > MAXG) N = lo;
        if (2 * N > MOORE || N > MAXG) break;
        double slice = left < 1.0 ? left : (left / 4 > 8.0 ? 8.0 : left / 4);
        int ok = attempt((int)N, now() + slice);
        if (ok) span = 1;
        else if (span < 8) span *= 2;
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d >= MAXD) {
        best.n = 0;
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    MOORE = moore_bound();
    if (d >= 3 && D >= 2 && best.n > 0) search(t_end);
    print_graph(&best);
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
RECORDS = {(3, 3): 14, (4, 8): 2184}


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


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    try:
        for cand in known_starts(d, D):
            n, e = cand
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, target],
                         stdin_graph=best, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
