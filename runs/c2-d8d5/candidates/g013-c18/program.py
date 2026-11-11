"""Bold variant: cyclic voltage lifts with orbit-reduced annealing (C) over base graphs of up to 8+8 vertices, then a grow-by-two polish (C)."""
import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine A: cyclic voltage lifts found by annealing over the base graph.
# Base: p A-vertices and p B-vertices, d perfect matchings (one per dart round t),
# each dart (t,i) joins A_i to B_{sig[t][i]} with voltage vol[t][i] in Z_N.
# Coverage is checked on the base only: for a cyclic regular cover, the lift has
# diameter <= D iff every base node is reached from every base source, with
# group elements tracked as an N-bit set (bit g = reached with voltage g).
# Each annealing move costs a few thousand word operations, so the search
# explores far more configurations than full-graph bitset evaluation.
# ----------------------------------------------------------------------------

VOLT_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define PMAX 8
#define NMAX 2048
#define WMAX (NMAX / 64)
#define DMAX 32
#define VMAX (2 * PMAX)
#define PEN 40

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

static int P, N, W;
static uint64_t topmask;
static int sig[DMAX][PMAX];
static int vol[DMAX][PMAX];
static int bsig[DMAX][PMAX], bvol[DMAX][PMAX];
static int bestP, bestN;
static uint64_t RA[VMAX * VMAX * WMAX], RB[VMAX * VMAX * WMAX];
static uint64_t t1[WMAX], t2[WMAX];

#define RI(s, nd) ((size_t)((s) * VMAX + (nd)) * WMAX)

/* y = x << s, truncated to N bits. */
static void shl_words(const uint64_t *x, int s, uint64_t *y) {
    int ws = s >> 6, bs = s & 63;
    for (int i = W - 1; i >= 0; i--) {
        int j = i - ws;
        uint64_t v = 0;
        if (j >= 0) {
            v = x[j] << bs;
            if (bs && j - 1 >= 0) v |= x[j - 1] >> (64 - bs);
        }
        y[i] = v;
    }
    y[W - 1] &= topmask;
}

/* y = x >> s. */
static void shr_words(const uint64_t *x, int s, uint64_t *y) {
    int ws = s >> 6, bs = s & 63;
    for (int i = 0; i < W; i++) {
        int j = i + ws;
        uint64_t v = 0;
        if (j < W) {
            v = x[j] >> bs;
            if (bs && j + 1 < W) v |= x[j + 1] << (64 - bs);
        }
        y[i] = v;
    }
}

/* dst |= rotate(x, s) within Z_N, i.e. bit g moves to g + s mod N. */
static void rot_or(uint64_t *dst, const uint64_t *x, int s) {
    if (s == 0) {
        for (int w = 0; w < W; w++) dst[w] |= x[w];
        return;
    }
    shl_words(x, s, t1);
    shr_words(x, N - s, t2);
    for (int w = 0; w < W; w++) dst[w] |= t1[w] | t2[w];
}

/* Sum over all (source base node, reached base node) of unreached group elements. */
static long coverage_cost(void) {
    int V = 2 * P;
    uint64_t *cur = RA, *nxt = RB;
    for (int s = 0; s < V; s++)
        for (int nd = 0; nd < V; nd++) {
            uint64_t *x = cur + RI(s, nd);
            for (int w = 0; w < W; w++) x[w] = 0;
        }
    for (int s = 0; s < V; s++) cur[RI(s, s)] = 1ULL;

    for (int r = 0; r < D; r++) {
        for (int s = 0; s < V; s++)
            for (int nd = 0; nd < V; nd++) {
                uint64_t *x = nxt + RI(s, nd);
                const uint64_t *y = cur + RI(s, nd);
                for (int w = 0; w < W; w++) x[w] = y[w];
            }
        for (int t = 0; t < d; t++)
            for (int i = 0; i < P; i++) {
                int a = i, b = P + sig[t][i], v = vol[t][i];
                int nv = (N - v) % N;
                for (int s = 0; s < V; s++) {
                    rot_or(nxt + RI(s, b), cur + RI(s, a), v);
                    rot_or(nxt + RI(s, a), cur + RI(s, b), nv);
                }
            }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }

    long unc = 0;
    for (int s = 0; s < V; s++)
        for (int nd = 0; nd < V; nd++) {
            const uint64_t *x = cur + RI(s, nd);
            long pop = 0;
            for (int w = 0; w < W; w++) pop += __builtin_popcountll(x[w]);
            unc += N - pop;
        }
    return unc;
}

/* Number of duplicate lift edges: same base pair and same voltage. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < P; i++)
        for (int ta = 0; ta < d; ta++)
            for (int tb = ta + 1; tb < d; tb++)
                if (sig[ta][i] == sig[tb][i] && vol[ta][i] == vol[tb][i]) c++;
    return c;
}

static long total_cost(void) { return coverage_cost() + PEN * dup_count(); }

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < P; i++) sig[t][i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = sig[t][i];
            sig[t][i] = sig[t][j];
            sig[t][j] = s;
        }
        for (int i = 0; i < P; i++) vol[t][i] = rndint(N);
    }
}

static long anneal(long iters) {
    random_state();
    long cur = total_cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)it / (double)iters) + 0.05;
        int t = rndint(d), i = rndint(P);
        if (rnd01() < 0.75) {
            int old = vol[t][i];
            int nv = rndint(N);
            if (nv == old) continue;
            vol[t][i] = nv;
            long c2 = total_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else vol[t][i] = old;
        } else {
            if (P < 2) continue;
            int i2 = rndint(P);
            if (i2 == i) continue;
            int s = sig[t][i];
            sig[t][i] = sig[t][i2];
            sig[t][i2] = s;
            long c2 = total_cost();
            if (c2 <= cur || rnd01() < exp((double)(cur - c2) / T)) cur = c2;
            else {
                s = sig[t][i];
                sig[t][i] = sig[t][i2];
                sig[t][i2] = s;
            }
        }
    }
    return cur;
}

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
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    long moore = moore_bound();
    long best_n = 0;
    int have = 0;

    if (d >= 2 && d <= DMAX && D >= 3) {
        while (now() < t_end && best_n < moore) {
            int p = 1 + rndint(PMAX);
            long need = best_n / (2L * p) + 1;   /* smallest N with 2pN > best_n */
            long Nt = need + rndint(2);
            if (Nt < 1 || Nt > NMAX || 2L * p * Nt > moore || 2L * p * Nt > 4096) continue;
            P = p;
            N = (int)Nt;
            W = (N + 63) / 64;
            int nb = N - 64 * (W - 1);
            topmask = nb == 64 ? ~0ULL : ((1ULL << nb) - 1);
            long c = anneal(6000);
            if (c == 0) {
                best_n = 2L * P * N;
                have = 1;
                bestP = P;
                bestN = N;
                for (int t = 0; t < d; t++)
                    for (int i = 0; i < P; i++) {
                        bsig[t][i] = sig[t][i];
                        bvol[t][i] = vol[t][i];
                    }
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    long m = (long)bestP * d * bestN;
    printf("%d %ld\n", 2 * bestP * bestN, m);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < bestP; i++) {
            int a = i, b = bestP + bsig[t][i], v = bvol[t][i];
            for (int x = 0; x < bestN; x++)
                printf("%d %d\n", a * bestN + x, b * bestN + (x + v) % bestN);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# C engine B: grow-by-two annealing with lift repair, from a valid start graph.
# ----------------------------------------------------------------------------

GROW_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid start), or "0 0".
 * stdout: "n m" + edge lines, the largest valid graph found.
 */
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
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
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Fills badv[v] = number of bad partners of v. */
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
        badv[v] = n - c;
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

/* Z_m x|_r Z_k: element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
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

typedef struct { int i, j, g; } Dart;

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
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

static int bad_list[MAXN];
static int badsave[MAXN];

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        /* Endpoint v: a random vertex that still lies in a bad pair (badv is current here). */
        int nbad = 0;
        for (int w = 0; w < work->n; w++)
            if (badv[w] > 0) bad_list[nbad++] = w;
        int v = nbad ? bad_list[rndint(nbad)] : rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        memcpy(badsave, badv, sizeof(int) * work->n);
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
            memcpy(badv, badsave, sizeof(int) * work->n);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double lift_share = had_start ? 0.2 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (C): cyclic voltage lifts over base graphs of up to 8+8 vertices.
    if D >= 3:
        volt_budget = 0.55 * (end - time.monotonic())
        if volt_budget > 1.0:
            try:
                text = lib.run_c(VOLT_SOURCE, [d, D, seed, round(volt_budget, 2)],
                                 timeout=volt_budget + 8)
                consider(*lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    # Phase 2 (C): lift + grow-by-two from the best graph so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(GROW_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=best, timeout=c_budget + 8)
                consider(*lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
