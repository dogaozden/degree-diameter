"""Combined program, v3 (bold change for the weak d=3, D=9 case).

Instead of growing a graph vertex by vertex, the C engine now searches bi-Cayley graphs over
metacyclic groups Z_m x|_r Z_k (one vertex per side, d voltages, g_0 = e). For each order N,
ascending from the current record, it runs an exhaustive cyclic scan when d = 3, then
simulated annealing over the voltages of random groups of order N. The objective is the
number of vertices unreached within D from a_e and b_e. Left multiplication is an automorphism
that is regular on each side, so those two BFS runs cover every pair. Every candidate is
re-checked by a full all-pairs BFS before it is accepted. Python keeps the algebraic starts
and returns the best graph that lib.is_valid accepts, so a valid fallback always exists.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley voltage search over semidirect groups, v3.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A-vertex x ~ B-vertex x*g_t (g_0 = e, distinct g_t), G = Z_m x|_r Z_k of order N.
 * Vertex layout: A-vertex x -> x, B-vertex y -> N + y.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NMAX 1200
#define MAXV (2 * NMAX)
#define MAXD 32
#define MAXGRP 4096
#define EVALS 30000

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

typedef struct { int m, k, r; } Tri;

static int d, D;
static double t_end;
static double span_slice;
static Graph best, cand;

static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static int vd[MAXV], vq[MAXV];

/* Full validity: degree, simple, bipartite sides, every pair within D. */
static int full_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXV) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) vd[v] = -1;
        int head = 0, tail = 0;
        vd[s] = 0;
        vq[tail++] = s;
        while (head < tail) {
            int v = vq[head++];
            if (vd[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (vd[u] < 0) { vd[u] = vd[v] + 1; vq[tail++] = u; }
            }
        }
        if (tail < n) return 0;
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 0; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    static int stk[MAXV];
    static unsigned char seen[MAXV];
    memset(seen, 0, sizeof seen);
    for (int s = 0; s < n; s++) {
        if (seen[s]) continue;
        seen[s] = 1;
        g->side[s] = 0;
        int top = 0;
        stk[top++] = s;
        while (top) {
            int v = stk[--top];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (!seen[u]) {
                    seen[u] = 1;
                    g->side[u] = 1 - g->side[v];
                    stk[top++] = u;
                }
            }
        }
    }
    if (!full_valid(g)) g->n = 0;
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

/* ---------------------------------------------------------- groups */

static Tri grp[MAXGRP];
static int ngrp;
static int MUL[NMAX * NMAX];
static int INV[NMAX];
static int curN;
static int gs[MAXD], gi[MAXD];
static int nd;

static void add_tri(int m, int k, int r) {
    if (ngrp < MAXGRP) {
        grp[ngrp].m = m;
        grp[ngrp].k = k;
        grp[ngrp].r = r;
        ngrp++;
    }
}

/* All semidirect groups Z_m x|_r Z_k with m*k = N (cyclic is included as m = N, r = 1). */
static void list_groups(int N) {
    ngrp = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_tri(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            add_tri(m, k, r);
        }
    }
}

/* Multiplication table and inverses for the group described by t (element a*k+b). */
static void build_group(int N, Tri t) {
    static int rp[NMAX];
    int m = t.m, k = t.k, r = t.r;
    curN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int za = (int)((a + (long)rp[b] * c) % m);
            MUL[x * N + y] = za * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------ bi-Cayley evaluation */

static int bstamp[MAXV], bdist[MAXV], bq[MAXV];
static int stampc = 0;

/* Number of vertices not reached within D from a_e and from b_e (0 means valid). */
static int eval_bad(void) {
    int N = curN, nv = 2 * N, bad = 0;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        if (stampc >= 1000000000) { memset(bstamp, 0, sizeof bstamp); stampc = 0; }
        stampc++;
        int head = 0, tail = 0;
        bstamp[src] = stampc;
        bdist[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            if (bdist[v] >= D) continue;
            int dv = bdist[v] + 1;
            for (int t = 0; t < nd; t++) {
                int u = (v < N) ? N + MUL[v * N + gs[t]] : MUL[(v - N) * N + gi[t]];
                if (bstamp[u] != stampc) {
                    bstamp[u] = stampc;
                    bdist[u] = dv;
                    bq[tail++] = u;
                }
            }
        }
        bad += nv - tail;
    }
    return bad;
}

/* Simulated annealing over voltages g_1..g_{d-1} for the current group. */
static int anneal(int steps, double until) {
    int N = curN;
    nd = d;
    gs[0] = 0;
    for (int t = 1; t < d; t++) {
        for (;;) {
            int g = 1 + rndint(N - 1), ok = 1;
            for (int u = 0; u < t; u++)
                if (gs[u] == g) { ok = 0; break; }
            if (ok) { gs[t] = g; break; }
        }
    }
    for (int t = 0; t < d; t++) gi[t] = INV[gs[t]];
    int cur = eval_bad();
    double T = 1.0;
    for (int s = 0; s < steps && cur > 0; s++) {
        if ((s & 1023) == 0 && now() > until) return -1;
        int t = 1 + rndint(d - 1);
        int old = gs[t], g;
        for (;;) {
            g = 1 + rndint(N - 1);
            int ok = 1;
            for (int u = 0; u < d; u++)
                if (gs[u] == g) { ok = 0; break; }
            if (ok) break;
        }
        gs[t] = g;
        gi[t] = INV[g];
        int nb = eval_bad();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            gs[t] = old;
            gi[t] = INV[old];
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return cur == 0;
}

/* d = 3, cyclic group, connection set {0, a, b}: exhaustive over a < b. */
static int exhaustive_cyclic(int N, double until) {
    build_group(N, (Tri){N, 1, 1});
    nd = 3;
    gs[0] = 0;
    gi[0] = 0;
    long cnt = 0;
    for (int a = 1; a < N; a++)
        for (int b = a + 1; b < N; b++) {
            if ((++cnt & 255) == 0 && now() > until) return 0;
            gs[1] = a;
            gs[2] = b;
            gi[1] = INV[a];
            gi[2] = INV[b];
            if (eval_bad() == 0) return 1;
        }
    return 0;
}

static void build_graph(Graph *g, int N) {
    g->n = 2 * N;
    for (int v = 0; v < 2 * N; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            add_edge(g, x, N + MUL[x * N + gs[t]]);
}

/* Build the candidate from gs (current group) and keep it if it is valid and larger. */
static int try_accept(int N) {
    build_graph(&cand, N);
    if (cand.n > best.n && full_valid(&cand)) {
        memcpy(&best, &cand, sizeof(Graph));
        return 1;
    }
    return 0;
}

/* Ascending search over N = lo..hi, each N given a short time slice. */
static void search(int lo, int hi, double until) {
    long moore = moore_bound();
    for (int N = lo; N <= hi && now() < until; N++) {
        if (2L * N > moore) break;
        if (N < d + 1) continue;
        double slice_end = now() + span_slice;
        if (slice_end > until) slice_end = until;
        list_groups(N);
        if (ngrp == 0) continue;
        int found = 0;
        if (d == 3 && exhaustive_cyclic(N, slice_end)) found = try_accept(N);
        while (!found && now() < slice_end) {
            build_group(N, grp[rndint(ngrp)]);
            if (anneal(EVALS, slice_end) == 1) found = try_accept(N);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0 && D >= 2) complete_bipartite(&best);
    if (best.n == 0) { printf("0 0\n"); return 0; }

    long moore = moore_bound();
    if (d >= 3 && D >= 2 && (long)best.n < moore) {
        double span = t_end - t0;
        span_slice = span / 20.0;
        if (span_slice < 0.3) span_slice = 0.3;
        int base = best.n / 2 + 1;
        if (base < d + 1) base = d + 1;
        long nmax = moore / 2;
        if (nmax > NMAX) nmax = NMAX;
        search(base, (int)nmax, t_end);
    }
    print_graph(&best);
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
