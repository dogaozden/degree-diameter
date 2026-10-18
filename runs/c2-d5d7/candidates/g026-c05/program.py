"""Lift search for the d=5, D=7 target, with a new C engine.

The C engine searches voltage lifts of random d-regular bipartite base multigraphs with p fibres per
side (p = 1..6) over random admissible semidirect products Z_m x| Z_k. Each candidate is scored by an
orbit-reduced diameter count (one BFS per base-vertex fibre, exact because the group acts regularly
on each fibre) and improved by simulated annealing on the voltages. Every improvement is re-verified
with an exact bitset diameter check. Start graphs are the hexagon incidence graph H(q) (q = d-1 in
{2, 4}), projective-plane incidence graphs, and the Araujo-Pardo-Lopez graph where applicable, and
K_{d,d} is the last resort. Python keeps the largest candidate that passes lib.is_valid.
"""
import time
import itertools

import numpy as np

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 32
#define MAXP 8
#define MAXDART (MAXD * MAXP)
#define MAXGL 20000
#define STEPS 4000

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

static Graph best, cand;
static int d, D;
static double t_end;

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

static int gcd_i(int a, int b) {
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
        if (s > 1000000000L) break;
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

static uint64_t FA[(size_t)MAXV * (MAXV / 64)];
static uint64_t FB[(size_t)MAXV * (MAXV / 64)];

/* Exact number of unordered pairs at distance > D (bitset BFS). */
static long full_bad(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = FA, *nxt = FB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int graph_ok(const Graph *g) {
    if (g->n < 2 || g->n > MAXV) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return full_bad(g) == 0;
}

static int read_start(Graph *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXV * MAXD) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= MAXD || g->deg[v] >= MAXD) return 0;
        add_edge(g, u, v);
    }
    static int queue[MAXV];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
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

/* ---------- groups Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e) ---------- */

typedef struct { int m, k, r; } GDesc;
static GDesc glist[MAXGL];
static int gcount;
static int rpw[MAXV];
static int GM, GK, GR;

static int gmul_(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rpw[b] * c) % GM) * GK + (b + e) % GK;
}

static int ginv_(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)(((long)rpw[nb] * a) % GM);
    na = (GM - na) % GM;
    return na * GK + nb;
}

static void enum_groups(int N) {
    gcount = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (gcount < MAXGL) {
                glist[gcount].m = m;
                glist[gcount].k = k;
                glist[gcount].r = r;
                gcount++;
            }
        }
    }
}

static void pick_group(void) {
    int idx = rndint(gcount);
    if (rnd01() < 0.7) {
        for (int tries = 0; tries < 30; tries++) {
            int c = rndint(gcount);
            if (glist[c].m > 1 && glist[c].k > 1 && glist[c].r != 1) { idx = c; break; }
        }
    }
    GM = glist[idx].m;
    GK = glist[idx].k;
    GR = glist[idx].r;
    rpw[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rpw[b] = (int)((long)rpw[b - 1] * GR % GM);
}

/* ---------- base multigraph and voltages ---------- */

static int GP, GN, GV;
static int nd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART], dGI[MAXDART];
static int ffA[MAXP][MAXD], ffB[MAXP][MAXD];
static int ffAc[MAXP], ffBc[MAXP];

/* Random d-regular bipartite base on p + p nodes (union of d permutations), connected. */
static void make_base(int p) {
    for (;;) {
        nd = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) { dI[nd] = i; dJ[nd] = perm[i]; nd++; }
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, cnt = 1;
        for (int i = 0; i < 2 * MAXP; i++) seen[i] = 0;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int t = 0; t < nd; t++) {
                int a = dI[t], b = p + dJ[t];
                int u = -1;
                if (v == a) u = b;
                else if (v == b) u = a;
                if (u >= 0 && !seen[u]) { seen[u] = 1; cnt++; st[top++] = u; }
            }
        }
        if (cnt == 2 * p) break;
    }
    for (int i = 0; i < p; i++) { ffAc[i] = 0; ffBc[i] = 0; }
    for (int t = 0; t < nd; t++) {
        ffA[dI[t]][ffAc[dI[t]]++] = t;
        ffB[dJ[t]][ffBc[dJ[t]]++] = t;
    }
}

/* Voltage for dart t: fresh in [0, GN), not equal to another dart on the same fibre pair. */
static int fresh_g(int t) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != t && dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void init_volt(void) {
    for (int t = 0; t < nd; t++) dG[t] = -1;
    for (int t = 0; t < nd; t++) {
        dG[t] = fresh_g(t);
        dGI[t] = ginv_(dG[t]);
    }
}

/* Orbit-reduced count: for each of the 2p fibre representatives, unreached vertices. */
static int bfs_stamp[MAXV], bfs_dist[MAXV], bfs_q[MAXV];
static int bstamp = 0;

static long eval_bad(void) {
    int p = GP, N = GN, V = GV;
    long total = 0;
    for (int src = 0; src < 2 * p; src++) {
        bstamp++;
        int head = 0, tail = 0;
        int s = src * N;
        bfs_stamp[s] = bstamp;
        bfs_dist[s] = 0;
        bfs_q[tail++] = s;
        while (head < tail) {
            int v = bfs_q[head++];
            int dv = bfs_dist[v];
            if (dv >= D) continue;
            int fib = v / N, x = v % N;
            if (fib < p) {
                for (int c = 0; c < ffAc[fib]; c++) {
                    int t = ffA[fib][c];
                    int u = (p + dJ[t]) * N + gmul_(x, dG[t]);
                    if (bfs_stamp[u] != bstamp) {
                        bfs_stamp[u] = bstamp;
                        bfs_dist[u] = dv + 1;
                        bfs_q[tail++] = u;
                    }
                }
            } else {
                int j = fib - p;
                for (int c = 0; c < ffBc[j]; c++) {
                    int t = ffB[j][c];
                    int u = dI[t] * N + gmul_(x, dGI[t]);
                    if (bfs_stamp[u] != bstamp) {
                        bfs_stamp[u] = bstamp;
                        bfs_dist[u] = dv + 1;
                        bfs_q[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Simulated annealing on the voltages of the current base and group. */
static long anneal(double until) {
    long bad = eval_bad();
    double T = 3.0, Tend = 0.2;
    double alpha = pow(Tend / T, 1.0 / STEPS);
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int oldg = dG[t], oldgi = dGI[t];
        int ng = fresh_g(t);
        dG[t] = ng;
        dGI[t] = ginv_(ng);
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dG[t] = oldg;
            dGI[t] = oldgi;
        }
        T *= alpha;
        if (T < Tend) T = Tend;
    }
    return bad;
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element y -> (p+j)*N + y. */
static void build_full(Graph *g) {
    int p = GP, N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (p + dJ[t]) * N + gmul_(x, dG[t]));
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
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD - 1 || D < 1) {
        printf("1 0\n");
        return 0;
    }

    if (!read_start(&best) || !graph_ok(&best)) complete_bipartite(&best);
    if (!graph_ok(&best)) { printf("1 0\n"); return 0; }

    long moore = moore_bound();
    while (now() < t_end && best.n + 2 <= moore && best.n + 2 <= MAXV) {
        int p = 1 + rndint(6);
        long N = (best.n + 2 + 2L * p - 1) / (2L * p);
        N += rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXV) continue;

        enum_groups((int)N);
        if (gcount == 0) continue;
        pick_group();
        GP = p;
        GN = (int)N;
        GV = 2 * p * (int)N;
        make_base(p);
        init_volt();
        long bad = anneal(t_end);
        if (bad == 0) {
            build_full(&cand);
            if (cand.n > best.n && graph_ok(&cand)) best = cand;
        }
    }

    if (!graph_ok(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
