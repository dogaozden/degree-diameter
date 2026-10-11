"""Haar-graph difference search for D = 3, seeded by the best known start graph.

A Haar graph H(Z_m, S) has parts a_i and b_i (i in Z_m), with a_i ~ b_{i+s} for s in S, |S| = d.
It is bipartite and d-regular with 2m vertices. Its diameter is at most 3 exactly when
  (1) every nonzero x in Z_m is a difference s1 - s2 (s1, s2 in S), and
  (2) every y in Z_m is s1 - s2 + s3 (s1, s2, s3 in S).
The C engine searches for such S by simulated annealing for m = L, L+1, ... and keeps the
largest valid graph. Python supplies the start: a projective-plane or Araujo-Pardo-Lopez
graph when available, otherwise the largest projective plane with degree <= d. For
d = 16 that is PG(2,13), 366 vertices, which already beats the parent's 318.
Every output is re-checked in C and again with lib.is_valid in Python.
"""
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

#define MAXN 4096
#define MAXD 64

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static int d, D;
static double t_end;
static Graph best, cand;
static int Sbest[MAXD];
static int dd[MAXN], tri[MAXN];
static int que[MAXN], dist[MAXN];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static int has_nbr(const Graph *g, int v, int u) {
    for (int i = 0; i < g->deg[v]; i++)
        if (g->adj[v][i] == u) return 1;
    return 0;
}

/* Full check: simple, symmetric, degree <= d, connected, diameter <= D, bipartite. */
static int check_valid(const Graph *g) {
    int n = g->n;
    if (n < 1 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || !has_nbr(g, u, v)) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s] = 0;
        que[t++] = s;
        while (h < t) {
            int v = que[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    que[t++] = u;
                }
            }
        }
        if (t != n) return 0;
        for (int v = 0; v < n; v++)
            if (dist[v] > D) return 0;
        if (s == 0) {
            /* connected + every edge joins different BFS parity  <=>  bipartite */
            for (int v = 0; v < n; v++)
                for (int i = 0; i < g->deg[v]; i++)
                    if (((dist[g->adj[v][i]] ^ dist[v]) & 1) == 0) return 0;
        }
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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
    if (!check_valid(g)) g->n = 0;
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

/* K_{a,a} with parts 0..a-1 and a..2a-1. */
static void complete_bip(Graph *g, int a) {
    g->n = 2 * a;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int x = 0; x < a; x++)
        for (int y = 0; y < a; y++) add_edge(g, x, a + y);
}

/* Cost of the set s (size d, residues mod m): uncovered nonzero differences plus
 * uncovered elements of S - S + S. Zero means H(Z_m, S) has diameter <= 3. */
static int cover_cost(const int *s, int m) {
    for (int x = 0; x < m; x++) dd[x] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) dd[(s[i] - s[j] + m) % m] = 1;
    dd[0] = 1;
    for (int x = 0; x < m; x++) tri[x] = 0;
    for (int x = 0; x < m; x++)
        if (dd[x])
            for (int k = 0; k < d; k++) tri[(x + s[k]) % m] = 1;
    int cost = 0;
    for (int x = 0; x < m; x++) {
        cost += !dd[x];
        cost += !tri[x];
    }
    return cost;
}

/* Simulated annealing with restarts for a set S of size d in Z_m. */
static int find_set(int m, double deadline) {
    int cur[MAXD], nxt[MAXD];
    const int STEPS = 40000;
    const double T0 = 1.0, T1 = 0.03;
    const double f = pow(T1 / T0, 1.0 / STEPS);
    while (now() < deadline) {
        int i = 0;
        while (i < d) {
            int x = rndint(m), dup = 0;
            for (int j = 0; j < i; j++)
                if (cur[j] == x) { dup = 1; break; }
            if (!dup) cur[i++] = x;
        }
        int cost = cover_cost(cur, m);
        double T = T0;
        for (int st = 0; st < STEPS && cost > 0; st++) {
            if ((st & 255) == 0 && now() > deadline) return 0;
            int k = rndint(d), x = rndint(m), dup = 0;
            for (int j = 0; j < d; j++)
                if (cur[j] == x) { dup = 1; break; }
            if (!dup) {
                memcpy(nxt, cur, sizeof(int) * d);
                nxt[k] = x;
                int nc = cover_cost(nxt, m);
                if (nc <= cost || rnd01() < exp((cost - nc) / T)) {
                    memcpy(cur, nxt, sizeof(int) * d);
                    cost = nc;
                }
            }
            T *= f;
        }
        if (cost == 0) {
            memcpy(Sbest, cur, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

static void build_haar(Graph *g, int m) {
    g->n = 2 * m;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int i = 0; i < m; i++)
        for (int k = 0; k < d; k++)
            add_edge(g, i, m + (i + Sbest[k]) % m);
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) {
        best.n = 1;
        best.deg[0] = 0;
        print_graph(&best);
        return 0;
    }

    read_start(&best);
    if (best.n == 0) complete_bip(&best, D >= 2 ? d : 1);
    if (!check_valid(&best)) complete_bip(&best, 1);

    if (D == 3 && d >= 2) {
        int L = best.n / 2 + 1;
        if (L < d) L = d;
        int mmax = 1 + d * (d - 1);
        if (mmax > MAXN / 2) mmax = MAXN / 2;
        for (int m = L; m <= mmax; m++) {
            double tn = now();
            if (tn > t_end) break;
            double cap = 0.25 * (t_end - tn);
            if (cap < 2.0) cap = 2.0;
            double dl = tn + cap;
            if (dl > t_end) dl = t_end;
            if (find_set(m, dl)) {
                build_haar(&cand, m);
                if (cand.n > best.n && check_valid(&cand)) best = cand;
            }
        }
    }

    if (!check_valid(&best)) complete_bip(&best, 1);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best algebraic start for (d, D), or None. Only D = 3 has constructions here."""
    if D != 3:
        return None
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)     # Moore graph: optimal
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)             # record graphs of order 2(q^2+q+5)
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]   # q + 1 <= d
    if qs:
        return lib.projective_plane_incidence(qs[-1])    # degree q+1 <= d, order 2(q^2+q+1)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)]) if lib.is_valid(2, [(0, 1)], d, D) else (1, [])

    budget = 0.85 * time_limit - 1.5 - (time.monotonic() - t0)
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the engine

    if D == 3 and d >= 2 and budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=best, timeout=budget + 10)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
