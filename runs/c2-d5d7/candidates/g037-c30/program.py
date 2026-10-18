"""Multi-fibre group-lift search for the d=5, D=7 target.

This version replaces the single-fibre bi-Cayley hill-climb with a different construction.
The graph is a lift of a small random d-regular bipartite base multigraph with p <= 3 fibres
per side, over a random semidirect product Z_m x| Z_k. The vertex count is 2pN. Each lift is
scored by an orbit-reduced BFS: since the group acts transitively on every fibre, it is enough
to run one BFS per fibre from its identity element. Each candidate is simulated-annealed on its
voltages, then verified in C by a full bitset diameter check. Start graphs come from the split
Cayley hexagon H(q) or the other algebraic constructions, and build() keeps only candidates that
pass lib.is_valid, so every case still returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre group-lift search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXG 2048
#define MAXD 32
#define MAXP 3
#define MAXW (MAXN / 64)
#define STEPS 2500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best, cand;

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (bitset BFS on all sources). */
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

/* ---------------- semidirect group Z_m x|_r Z_k ----------------
 * Element a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */

static int MT[MAXG * MAXG];   /* MT[x*N + y] = x*y */
static int INV[MAXG];
static int NN;

static void build_mt(int m, int k, int r) {
    int N = m * k;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    NN = N;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
}

/* Uniformly sample an admissible (m, k, r) with m*k = N (reservoir sampling). */
static int sample_group(int N, int *pm, int *pk, int *pr) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    *pm = bm; *pk = bk; *pr = br;
    return 1;
}

/* ---------------- multi-fibre lift ----------------
 * p fibres on each side. A-fibre i vertex (i, x) = i*N + x, B-fibre j vertex (j, y) = (p+j)*N + y.
 * Dart t = (DI, DJ, DG) joins (DI, x) to (DJ, x*DG) for every x in G.
 * Every A fibre has d darts out, every B fibre d darts in (base is d-regular). */

static int P_, ND;
static int DI[MAXD * MAXP], DJ[MAXD * MAXP], DG[MAXD * MAXP];
static int OUTD[MAXP][MAXD], INDART[MAXP][MAXD];

static int clash(int t, int g) {
    for (int u = 0; u < ND; u++)
        if (u != t && DI[u] == DI[t] && DJ[u] == DJ[t] && DG[u] == g) return 1;
    return 0;
}

/* Random connected d-regular base multigraph on p + p vertices, with random distinct voltages. */
static int make_darts(int p) {
    for (int attempt = 0; attempt < 60; attempt++) {
        int M[MAXP][MAXP];
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns != 2 * p) continue;
        ND = 0;
        for (int i = 0; i < p; i++)
            for (int j = 0; j < p; j++)
                for (int c = 0; c < M[i][j]; c++) {
                    int t = ND++;
                    DI[t] = i;
                    DJ[t] = j;
                    do { DG[t] = rndint(NN); } while (clash(t, DG[t]));
                }
        int rc[MAXP] = {0}, cc[MAXP] = {0};
        for (int t = 0; t < ND; t++) {
            OUTD[DI[t]][rc[DI[t]]++] = t;
            INDART[DJ[t]][cc[DJ[t]]++] = t;
        }
        return 1;
    }
    return 0;
}

/* Orbit-reduced objective: unreached (source, vertex) pairs over one identity per fibre.
 * Zero iff the lift has diameter <= D (transitivity of left multiplication on fibres). */
static int mark[MAXN], bdist[MAXN], bq[MAXN];
static int mstamp = 0;

static long orbit_bad(void) {
    int p = P_, N = NN, V = 2 * p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        int head = 0, tail = 0;
        mstamp++;
        mark[src] = mstamp;
        bdist[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = bdist[v];
            if (dv >= D) continue;
            if (v < p * N) {
                int i = v / N, x = v % N;
                for (int k = 0; k < d; k++) {
                    int t = OUTD[i][k];
                    int u = (p + DJ[t]) * N + MT[x * N + DG[t]];
                    if (mark[u] != mstamp) {
                        mark[u] = mstamp;
                        bdist[u] = dv + 1;
                        bq[tail++] = u;
                    }
                }
            } else {
                int j = v / N - p, y = v % N;
                for (int k = 0; k < d; k++) {
                    int t = INDART[j][k];
                    int u = DI[t] * N + MT[y * N + INV[DG[t]]];
                    if (mark[u] != mstamp) {
                        mark[u] = mstamp;
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

/* Simulated annealing on the voltages of the current base. Returns the final objective.
 * The state is left as the final voltage set; it is valid iff the return value is 0. */
static long anneal(double until) {
    long bad = orbit_bad();
    double T = 1.2;
    double alpha = pow(0.02 / 1.2, 1.0 / STEPS);
    for (int s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(ND), old = DG[t], g;
        do { g = rndint(NN); } while (g == old || clash(t, g));
        DG[t] = g;
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else DG[t] = old;
        T *= alpha;
    }
    return bad;
}

static void build_lift(Graph *g) {
    int p = P_, N = NN, V = 2 * p * N;
    g->n = V;
    for (int v = 0; v < V; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, DI[t] * N + x, (p + DJ[t]) * N + MT[x * N + DG[t]]);
}

/* Repeatedly try multi-fibre lifts strictly larger than the incumbent. */
static void lift_search(double until) {
    long moore = moore_bound();
    int skips = 0;
    while (now() < until && skips < 400) {
        double u = rnd01();
        int p = u < 0.4 ? 1 : (u < 0.75 ? 2 : 3);
        long Nlo = best.n / (2 * p) + 1;
        if (Nlo < d + 1) Nlo = d + 1;
        long Nmax = moore / (2 * p);
        if (Nmax > MAXG) Nmax = MAXG;
        if (Nmax > MAXN / (2 * p)) Nmax = MAXN / (2 * p);
        if (Nlo > Nmax) { skips++; continue; }
        long span = Nmax - Nlo + 1;
        if (span > 80) span = 80;
        double w = rnd01();
        long N = Nlo + (long)(w * w * span);
        if (N > Nmax) N = Nmax;
        int m, k, r;
        if (!sample_group((int)N, &m, &k, &r)) { skips++; continue; }
        build_mt(m, k, r);
        P_ = p;
        if (!make_darts(p)) { skips++; continue; }
        if (anneal(until) == 0) {
            skips = 0;
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (d >= 3 && D >= 2 && best.n < moore_bound()) lift_search(t_end);

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

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so valid for D = 6 and D = 7.
    The caller validates the result with lib.is_valid.
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
