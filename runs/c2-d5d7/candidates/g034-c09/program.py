"""Multi-fibre group-lift search for the d=5, D=7 target.

Previous engine: bi-Cayley lifts (one A-fibre and one B-fibre) over semidirect products.
This version changes the construction. A lift has p A-fibres and p B-fibres over a group G
of order N (order 2pN). The base is a random connected d-regular bipartite multigraph on
p+p vertices, and each base dart carries a voltage in G. Voltages on a spanning tree of the
base are fixed to the identity, which is a gauge normalisation. The remaining voltages are
annealed to minimise the number of pairs at distance greater than D, counted from one
source per fibre. Left multiplication by G is an automorphism that is transitive on each
fibre, so these 2p sources are sufficient. Neighbours are computed implicitly from the
dart table, so no adjacency is rebuilt during the search.

Fibre counts p = 1..4 are mixed, so orders 2pN just above the incumbent are reached with
very different base structures. Near misses are polished by steepest descent. Each success
is verified by the C bitset check before it replaces the incumbent. The Python side returns
the best algebraic start (hexagon, generalized quadrangle, or K_{d,d}) whenever the C engine
fails, so every case returns a valid graph.
"""
import itertools
import time

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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXH 2048
#define MAXDART (MAXD * MAXP)
#define BC_STEPS 3000
#define BC_ATTEMPTS 6
#define POLISH_MAX 40
#define POLISH_SEC 2.0
#define SPAN 40

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int nd;
    int A[MAXDART], B[MAXDART], G[MAXDART], T[MAXDART];
} State;

static int d, D;
static double t_end;

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D, by bitsets. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
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

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------- groups: Z_m x|_r Z_k, element a*k+b ---------------- */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

static int pick_group(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* ---------------- darts of a multi-fibre lift ---------------- */
static int PP, NN, ND;
static int dA[MAXDART], dB[MAXDART], dG[MAXDART], dGi[MAXDART], dT[MAXDART];
static int adA[MAXP][MAXD], adB[MAXP][MAXD];
static int MTAB[MAXH * MAXH];
static int INVT[MAXH];

static void setup_group(int N, const Grp *G) {
    NN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[(size_t)x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INVT[x] = y; break; }
}

/* Random d-regular bipartite base multigraph on p+p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stk[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        stk[top++] = 0;
        while (top) {
            int v = stk[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; stk[top++] = u; }
            }
        }
        if (ns == 2 * p) return;
    }
}

static void rebuild_adj(void) {
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < ND; t++) {
        dGi[t] = INVT[dG[t]];
        adA[dA[t]][ca[dA[t]]++] = t;
        adB[dB[t]][cb[dB[t]]++] = t;
    }
}

/* True if dart t's voltage g clashes with another dart on the same base pair. */
static int clash(int t, int g) {
    for (int u = 0; u < ND; u++)
        if (u != t && dA[u] == dA[t] && dB[u] == dB[t] && dG[u] == g) return 1;
    return 0;
}

/* Fresh base multigraph on p fibres per side; tree darts get voltage 0. */
static void new_darts(int p) {
    int M[MAXP][MAXP];
    make_base(p, M);
    int first[MAXP][MAXP];
    ND = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++) first[i][j] = -1;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                if (c == 0) first[i][j] = ND;
                dA[ND] = i; dB[ND] = j; dG[ND] = 0; dT[ND] = 0;
                ND++;
            }
    int seen[2 * MAXP] = {0}, q[2 * MAXP], h = 0, tl = 0;
    seen[0] = 1;
    q[tl++] = 0;
    while (h < tl) {
        int v = q[h++];
        if (v < p) {
            for (int j = 0; j < p; j++) {
                int u = p + j;
                if (!seen[u] && M[v][j]) { seen[u] = 1; q[tl++] = u; dT[first[v][j]] = 1; }
            }
        } else {
            int jj = v - p;
            for (int i = 0; i < p; i++) {
                if (!seen[i] && M[i][jj]) { seen[i] = 1; q[tl++] = i; dT[first[i][jj]] = 1; }
            }
        }
    }
    for (int t = 0; t < ND; t++) {
        if (dT[t]) continue;
        int g;
        do { g = rndint(NN); } while (g == 0 || clash(t, g));
        dG[t] = g;
    }
    rebuild_adj();
}

static void save_state(State *s) {
    s->nd = ND;
    for (int t = 0; t < ND; t++) {
        s->A[t] = dA[t]; s->B[t] = dB[t]; s->G[t] = dG[t]; s->T[t] = dT[t];
    }
}

static void load_state(const State *s) {
    ND = s->nd;
    for (int t = 0; t < ND; t++) {
        dA[t] = s->A[t]; dB[t] = s->B[t]; dG[t] = s->G[t]; dT[t] = s->T[t];
    }
    rebuild_adj();
}

static void redraw_one(void) {
    int fr[MAXDART], nf = 0;
    for (int t = 0; t < ND; t++) if (!dT[t]) fr[nf++] = t;
    if (!nf) return;
    int t = fr[rndint(nf)], g;
    do { g = rndint(NN); } while (g == dG[t] || clash(t, g));
    dG[t] = g;
    dGi[t] = INVT[g];
}

/* Bad ordered (source, vertex) pairs at distance > D; sources are element 0 of each fibre. */
static int bq[MAXN], bdist[MAXN], bseen[MAXN];
static int bstamp = 0;

static long eval_bad(void) {
    int V = 2 * PP * NN;
    int AV = PP * NN;
    long total = 0;
    for (int s = 0; s < 2 * PP; s++) {
        int src = s * NN;
        bstamp++;
        int head = 0, tail = 0;
        bseen[src] = bstamp;
        bdist[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = bdist[v];
            if (dv >= D) continue;
            if (v < AV) {
                int i = v / NN, x = v - i * NN;
                const int *row = MTAB + (size_t)x * NN;
                for (int k = 0; k < d; k++) {
                    int t = adA[i][k];
                    int u = (PP + dB[t]) * NN + row[dG[t]];
                    if (bseen[u] != bstamp) {
                        bseen[u] = bstamp;
                        bdist[u] = dv + 1;
                        bq[tail++] = u;
                    }
                }
            } else {
                int jf = v / NN;
                int y = v - jf * NN;
                int j = jf - PP;
                const int *row = MTAB + (size_t)y * NN;
                for (int k = 0; k < d; k++) {
                    int t = adB[j][k];
                    int u = dA[t] * NN + row[dGi[t]];
                    if (bseen[u] != bstamp) {
                        bseen[u] = bstamp;
                        bdist[u] = dv + 1;
                        bq[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage search on the current base. Leaves the best state in place. */
static long climb(double until) {
    static int bestG[MAXDART];
    int fr[MAXDART], nf = 0;
    for (int t = 0; t < ND; t++) if (!dT[t]) fr[nf++] = t;
    long bad = eval_bad();
    long bestb = bad;
    memcpy(bestG, dG, sizeof(int) * ND);
    if (nf == 0 || bad == 0) return bestb;
    double T = 2.0 * (1.0 + bad / 1000.0);
    double alpha = pow(0.2 / T, 1.0 / BC_STEPS);
    for (long s = 0; s < BC_STEPS && bad > 0; s++) {
        if (now() > until) break;
        int t = fr[rndint(nf)];
        int old = dG[t], g;
        do { g = rndint(NN); } while (g == old || clash(t, g));
        dG[t] = g;
        dGi[t] = INVT[g];
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(bestG, dG, sizeof(int) * ND);
            }
        } else {
            dG[t] = old;
            dGi[t] = INVT[old];
        }
        T *= alpha;
    }
    memcpy(dG, bestG, sizeof(int) * ND);
    for (int t = 0; t < ND; t++) dGi[t] = INVT[dG[t]];
    return bestb;
}

/* Steepest descent over single voltage replacements until no move helps or the deadline. */
static long polish(long bad, double deadline) {
    while (bad > 0 && now() < deadline) {
        long bb = bad;
        int bt = -1, bg = -1;
        for (int t = 0; t < ND && now() < deadline; t++) {
            if (dT[t]) continue;
            int old = dG[t];
            for (int g = 0; g < NN; g++) {
                if (g == old || clash(t, g)) continue;
                dG[t] = g;
                dGi[t] = INVT[g];
                long nb = eval_bad();
                if (nb < bb) { bb = nb; bt = t; bg = g; }
                if (now() > deadline) break;
            }
            dG[t] = old;
            dGi[t] = INVT[old];
        }
        if (bt < 0) break;
        dG[bt] = bg;
        dGi[bt] = INVT[bg];
        bad = bb;
    }
    return bad;
}

static void build_graph(Graph *g) {
    int AV = PP * NN;
    g->n = 2 * AV;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= AV; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < NN; x++)
            add_edge(g, dA[t] * NN + x, (PP + dB[t]) * NN + MTAB[(size_t)x * NN + dG[t]]);
}

/* Search lifts of order 2pN > best->n, mixing fibre counts p = 1..4. */
static void lift_search(Graph *best, double until) {
    static State elite;
    static Grp G;
    static Graph cand;
    while (now() < until) {
        if (best->n + 2 > MAXN) return;
        int r = rndint(6);
        int p = r == 0 ? 1 : r <= 2 ? 2 : r <= 4 ? 3 : 4;
        int cap = MAXN / (2 * p);
        if (cap > MAXH) cap = MAXH;
        int Nlo = best->n / (2 * p) + 1;
        if (Nlo > cap) continue;
        int span = cap - Nlo + 1;
        if (span > SPAN) span = SPAN;
        double u = rnd01();
        int N = Nlo + (int)(u * sqrt(u) * span);
        if (N > cap) N = cap;
        if (!pick_group(N, &G)) continue;
        setup_group(N, &G);
        PP = p;
        int have = 0, ok = 0;
        long elite_bad = -1;
        for (int att = 0; att < BC_ATTEMPTS && now() < until && !ok; att++) {
            if (have && rnd01() < 0.6) {
                load_state(&elite);
                redraw_one();
            } else {
                new_darts(p);
            }
            long b = climb(until);
            if (b > 0 && b <= POLISH_MAX) {
                double pd = now() + POLISH_SEC;
                if (pd > until) pd = until;
                b = polish(b, pd);
            }
            if (b == 0) {
                build_graph(&cand);
                if (cand.n > best->n && is_valid(&cand)) {
                    copy_graph(best, &cand);
                    ok = 1;
                }
            }
            if (!have || b < elite_bad) {
                save_state(&elite);
                elite_bad = b;
                have = 1;
            }
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD - 1) {
        if (d < 1) d = 1;
        if (d > MAXD - 1) d = MAXD - 1;
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (d >= 2 && D >= 2 && best.n < moore_bound())
        lift_search(&best, t_end);

    if (!is_valid(&best)) complete_bipartite(&best);
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

    def attempt(fn):
        try:
            out.append(fn())
        except Exception:
            pass

    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        attempt(lambda: lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        attempt(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        attempt(lambda: _hexagon_incidence(d - 1))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            attempt(lambda: _gq_w(q))
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
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
