"""Bi-Cayley (Haar-type) search over groups of many orders for the weakest target (d=4, D=7).

Change from the parent: the C engine no longer runs voltage lifts over a random base multigraph.
It now searches bi-Cayley graphs directly. A bi-Cayley graph over a group G of order N has vertices
a_x, b_y (x, y in G) and edges a_x ~ b_{x s} for a connection set S of size d. Left multiplication
by G is an automorphism, so the full distance structure is determined by two BFS runs, from a_e and
from b_e, on a graph with 2N vertices. A simulated-annealing search over S uses the excess-distance
cost (sum of max(0, dist - D), unreached vertices charged 2) and is exact: cost 0 iff diameter <= D.

The group is drawn from three families: metacyclic Z_m x| Z_k (all admissible r), and direct products
of PSL(2,p) or PGL(2,p) (p = 5, 7, 11) with a cyclic group. The order N is sampled from a window just
above half of the current best order, biased toward small N. This makes a ladder: each success raises
the lower bound, and the search keeps climbing. The start graph and algebraic constructions in Python
are unchanged, and every result is re-checked with lib.is_valid before it is returned.
"""
import time
import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley (Haar-type) degree-diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Vertices a_x = x and b_y = N + y for x, y in a group G of order N.
 * Edges: a_x ~ b_{x*s} for s in S, |S| = d, S distinct.
 * Left multiplication is an automorphism, so only BFS from a_e and b_e is needed.
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
#define MAXG 1100
#define HS 8192
#define NB 5

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
    if (b < 0) b += m;
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

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
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

/* ---------------------------------------------------------------- groups
 * The current group is a full multiplication table GT[x*GN+y] with identity 0,
 * and GINV[x] is the inverse of x. */
static int GN;
static int GT[MAXG * MAXG];
static int GINV[MAXG];

typedef struct { unsigned char p[16]; } Perm;
static Perm ELEM[MAXG];
static uint64_t hkey[HS];
static int hval[HS];

static int *base_tab[NB];
static int base_ord[NB];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hval[h]) {
        if (hkey[h] == key) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = key;
    hval[h] = idx + 1;
}

/* Closure of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on P^1(F_p). */
static int perm_closure(int p, int pgl, int *orderp) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng++;
    }

    memset(hval, 0, sizeof hval);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *orderp = n;
    return 1;
}

static int *make_base_table(int p, int pgl, int *ordp) {
    int ord = 0;
    if (!perm_closure(p, pgl, &ord)) return NULL;
    int s = p + 1;
    int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
    if (!tab) return NULL;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static void init_bases(void) {
    static const int BP[NB] = {5, 5, 7, 7, 11};
    static const int BG[NB] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NB; b++) {
        int ord = 0;
        base_tab[b] = make_base_table(BP[b], BG[b], &ord);
        base_ord[b] = base_tab[b] ? ord : 0;
    }
}

/* Direct product of base group b with Z_k. */
static void set_product(int b, int k) {
    int o = base_ord[b], N = o * k;
    GN = N;
    const int *bt = base_tab[b];
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = bt[x * o + y] * k + (c + e) % k;
}

/* Z_m x|_r Z_k: (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void set_meta(int m, int k, int r) {
    int N = m * k;
    GN = N;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

static void compute_inv(void) {
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (GT[x * GN + y] == 0) { GINV[x] = y; break; }
}

/* Pick a random group of order N: a product of a base group with Z_k, or a metacyclic group
 * (uniform over admissible (m, r) pairs). Returns 0 if none exists. */
static int choose_group(int N) {
    int cand[NB], nc = 0;
    for (int b = 0; b < NB; b++)
        if (base_tab[b] && base_ord[b] > 0 && N % base_ord[b] == 0) cand[nc++] = b;
    if (nc > 0 && rnd01() < 0.5) {
        int b = cand[rndint(nc)];
        set_product(b, N / base_ord[b]);
        compute_inv();
        return 1;
    }
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    set_meta(bm, bk, br);
    compute_inv();
    return 1;
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int hdist[2 * MAXG], hq[2 * MAXG];

/* Excess-distance cost of the bi-Cayley graph with connection set S (size dd) over the
 * current group of order N. It is 0 iff the graph is connected with diameter <= D. */
static long haar_cost(const int *S, int dd, int N) {
    long total = 0;
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) hdist[v] = -1;
        int head = 0, tail = 0;
        hdist[s0] = 0;
        hq[tail++] = s0;
        while (head < tail) {
            int v = hq[head++];
            int dv = hdist[v];
            if (v < N) {
                for (int i = 0; i < dd; i++) {
                    int u = N + GT[v * N + S[i]];
                    if (hdist[u] < 0) { hdist[u] = dv + 1; hq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < dd; i++) {
                    int u = GT[y * N + GINV[S[i]]];
                    if (hdist[u] < 0) { hdist[u] = dv + 1; hq[tail++] = u; }
                }
            }
        }
        for (int v = 0; v < V; v++) {
            if (hdist[v] < 0) total += 2;
            else if (hdist[v] > D) total += hdist[v] - D;
        }
    }
    return total;
}

static int fresh_elem(const int *S, int dd, int N) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int j = 0; j < dd; j++)
            if (S[j] == g) { ok = 0; break; }
        if (ok) return g;
    }
}

/* Simulated annealing over connection sets S of size d in the current group (order N > d).
 * Each move replaces one element of S by a fresh element. Returns 1 and fills S on success. */
static int haar_try(int N, double until, int *Sout) {
    int dd = d;
    int cur_S[MAXD], best_S[MAXD];
    if (N <= dd) return 0;
    for (int i = 0; i < dd; i++) cur_S[i] = fresh_elem(cur_S, i, N);
    long cur = haar_cost(cur_S, dd, N);
    long best = cur;
    memcpy(best_S, cur_S, sizeof(int) * dd);
    double T0 = 1.0 + 0.1 * (double)cur;
    double T = T0;
    int stall = 0;
    for (long s = 0; best > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        int i = rndint(dd);
        int old = cur_S[i];
        cur_S[i] = fresh_elem(cur_S, dd, N);
        long nv = haar_cost(cur_S, dd, N);
        long delta = nv - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nv;
        } else {
            cur_S[i] = old;
        }
        if (cur < best) {
            best = cur;
            memcpy(best_S, cur_S, sizeof(int) * dd);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9995;
        if (T < 0.3) T = 0.3;
        if (stall > 4000) {
            memcpy(cur_S, best_S, sizeof(int) * dd);
            cur = best;
            T = T0;
            stall = 0;
        }
    }
    if (best == 0) memcpy(Sout, best_S, sizeof(int) * dd);
    return best == 0;
}

static void build_haar(Graph *g, int N, const int *S, int dd) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < dd; i++)
            add_edge(g, x, N + GT[x * N + S[i]]);
}

/* Climb the order ladder: sample N in [lo, hi] with lo just above half the best order, biased
 * toward small N. Each success raises lo. Groups are drawn from the families above. */
static void haar_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long hi = moore / 2;
    if (hi > MAXG) hi = MAXG;
    while (now() < until) {
        long lo = best->n / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > hi) return;
        long span = hi - lo;
        double u = rnd01() * rnd01();
        long N = lo + (long)(u * (double)(span + 1));
        if (N > hi) N = hi;
        if (!choose_group((int)N)) continue;
        int S[MAXD];
        double until2 = now() + 1.0 + 3.0 * rnd01();
        if (until2 > until) until2 = until;
        if (haar_try((int)N, until2, S)) {
            build_haar(&cand, (int)N, S, d);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        init_bases();
        haar_search(&best, t_end);
    }
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    # Use most of the case budget for the engine; keep a margin for startup and output.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
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
