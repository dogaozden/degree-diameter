"""Bi-Cayley search over non-metacyclic groups for the weakest target (d=4, D=7).

Bold change from the parent: instead of voltage lifts over base multigraphs with several
vertices per side, this version searches one-vertex-per-side bi-Cayley graphs. Vertices are
A_x and B_x for x in a group G of order N, and A_x ~ B_{x g_i} for d chosen generators g_i.
Left multiplication is an automorphism, so the diameter check needs only two BFS runs, from
A_e and B_e.

Groups come from four families: semidirect products Z_m x|_r Z_k, PSL(2,p) and PGL(2,p)
(p = 5, 7, 11) times Z_k, and abelian Z_a x Z_b. The C engine hill-climbs over generator
sets for each sampled group, keeps only verified graphs, and raises the target order each
time it succeeds. The start graph (K_{d,d}, PG incidence, W(q), or H(3)) is the fallback,
so every case still returns a valid graph. This design has not been measured on the target
case yet.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search: one vertex per side per group element, d generators.
 * Usage:  prog d D seed time_limit [min_n] < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found (or the start graph).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NMAX 1100
#define VMAX 2200
#define WMAX ((VMAX + 63) / 64)
#define MAXD 16
#define NB 5
#define HS 4096
#define PMAX 700
#define STEPS 1500
#define RESTARTS 3

typedef struct {
    int n;
    int deg[VMAX];
    int adj[VMAX][MAXD];
    unsigned char side[VMAX];
} Graph;

typedef struct { unsigned char p[16]; } Perm;

/* type 0: Z_a x|_r Z_b (a*b = N); type 1: base[a] x Z_b; type 2: Z_a x Z_b. */
typedef struct { int type, N, a, b, r; } Desc;

static int d, D;
static double t_end;
static int need_n;

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

static Graph best, cand;
static uint64_t RA[VMAX * WMAX], RB[VMAX * WMAX];

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
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
    if (g->n <= 0 || g->n > VMAX) return 0;
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

static void read_start(void) {
    static int ql[VMAX];
    int n, m;
    best.n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > VMAX) return;
    best.n = n;
    for (int v = 0; v < n; v++) { best.deg[v] = 0; best.side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            best.deg[u] >= MAXD || best.deg[v] >= MAXD) { best.n = 0; return; }
        add_edge(&best, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (best.side[s] != 255) continue;
        int h = 0, t = 0;
        best.side[s] = 0;
        ql[t++] = s;
        while (h < t) {
            int v = ql[h++];
            for (int i = 0; i < best.deg[v]; i++) {
                int u = best.adj[v][i];
                if (best.side[u] == 255) { best.side[u] = 1 - best.side[v]; ql[t++] = u; }
                else if (best.side[u] == best.side[v]) { best.n = 0; return; }
            }
        }
    }
    if (!is_valid(&best)) best.n = 0;
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

static long moore_bipartite(void) {
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

/* ---------------------------------------------------------------- base groups PSL/PGL(2,p) */
static Perm ELEM[PMAX];
static uint64_t hkey[HS];
static int hval[HS];
static int *btab[NB];
static int bord[NB];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 52);
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

static int perm_closure(int p, int pgl, int *ordp) {
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
                if (n >= PMAX) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *ordp = n;
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
        btab[b] = make_base_table(BP[b], BG[b], &bord[b]);
        if (!btab[b]) bord[b] = 0;
    }
}

/* ---------------------------------------------------------------- group multiplication table */
static int GN;
static int GT[NMAX * NMAX];
static int GINV[NMAX];
static int rp[NMAX];

static void build_group(const Desc *ds) {
    int N = ds->N;
    GN = N;
    if (ds->type == 0) {
        int m = ds->a, k = ds->b, r = ds->r;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
        for (int x = 0; x < N; x++) {
            int a1 = x / k, b1 = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                GT[x * N + y] = (int)((a1 + (long)rp[b1] * c) % m) * k + (b1 + e) % k;
            }
        }
    } else if (ds->type == 1) {
        int bi = ds->a, k = ds->b, o = bord[bi];
        const int *bt = btab[bi];
        for (int x = 0; x < N; x++) {
            int x1 = x / k, c = x % k;
            for (int y = 0; y < N; y++) {
                int y1 = y / k, e = y % k;
                GT[x * N + y] = bt[x1 * o + y1] * k + (c + e) % k;
            }
        }
    } else {
        int a = ds->a, b = ds->b;
        for (int x = 0; x < N; x++) {
            int i = x / b, j = x % b;
            for (int y = 0; y < N; y++) {
                int k1 = y / b, l = y % b;
                GT[x * N + y] = ((i + k1) % a) * b + (j + l) % b;
            }
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { GINV[x] = y; break; }
}

/* Sample a random group of order N from the families. Returns 0 on failure. */
static int sample_desc(int N, Desc *ds) {
    int kind = rndint(10);
    ds->N = N;
    if (kind < 3) {
        int bi = rndint(NB);
        if (!btab[bi]) return 0;
        int o = bord[bi];
        if (o == 0 || N % o) return 0;
        ds->type = 1;
        ds->a = bi;
        ds->b = N / o;
        ds->r = 0;
        return 1;
    }
    int divs[NMAX], nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)], k = N / m;
    if (kind == 9) {
        ds->type = 2; ds->a = m; ds->b = k; ds->r = 0;
        return 1;
    }
    int r = 0;
    if (m > 1) {
        r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1) return 0;
        if (powmod(r, k, m) != 1 % m) return 0;
    }
    ds->type = 0; ds->a = m; ds->b = k; ds->r = r;
    return 1;
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int dist_[VMAX], queue_[VMAX];

/* Unreached vertices from A_e and B_e within distance D. Zero iff the bi-Cayley graph has diameter <= D. */
static int cost_of(const int *g) {
    int N = GN, nv = 2 * N, bad = 0;
    for (int s = 0; s < 2; s++) {
        int src = s == 0 ? 0 : N;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[src] = 0;
        queue_[t++] = src;
        while (h < t) {
            int v = queue_[h++];
            if (dist_[v] >= D) continue;
            if (v < N) {
                const int *row = GT + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[g[i]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[t++] = u; }
                }
            } else {
                const int *row = GT + (size_t)(v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[GINV[g[i]]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[t++] = u; }
                }
            }
        }
        bad += nv - t;
    }
    return bad;
}

static int search_group(int *gout) {
    int N = GN;
    int g[MAXD];
    for (int rs = 0; rs < RESTARTS; rs++) {
        for (int i = 0; i < d; i++) {
            for (;;) {
                int h = rndint(N), dup = 0;
                for (int j = 0; j < i; j++) if (g[j] == h) { dup = 1; break; }
                if (!dup) { g[i] = h; break; }
            }
        }
        int c = cost_of(g);
        for (int st = 0; st < STEPS && c > 0; st++) {
            if ((st & 255) == 0 && now() > t_end) return 0;
            int i = rndint(d), h = rndint(N), dup = 0;
            for (int j = 0; j < d; j++) if (g[j] == h) { dup = 1; break; }
            if (dup) continue;
            int old = g[i];
            g[i] = h;
            int cc = cost_of(g);
            if (cc <= c || rnd01() < exp(-(double)(cc - c) / 0.7)) c = cc;
            else g[i] = old;
        }
        if (c == 0) {
            memcpy(gout, g, sizeof(int) * (size_t)d);
            return 1;
        }
    }
    return 0;
}

static int make_candidate(const int *g) {
    int N = GN;
    cand.n = 2 * N;
    for (int v = 0; v < cand.n; v++) {
        cand.deg[v] = 0;
        cand.side[v] = v >= N;
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(&cand, x, N + GT[x * N + g[i]]);
    return is_valid(&cand);
}

static void search(void) {
    long moore = moore_bipartite();
    long hi_l = moore / 2;
    if (hi_l > NMAX) hi_l = NMAX;
    long lo_l = best.n / 2 + 1;
    long need_lo = (need_n + 1) / 2;
    if (need_lo > lo_l) lo_l = need_lo;
    if (lo_l < d) lo_l = d;
    int lo = (int)lo_l, hi = (int)hi_l;
    int g[MAXD];
    Desc ds;
    long spins = 0;
    while (lo <= hi && now() < t_end) {
        int span = hi - lo + 1;
        int N = (span > 40 && rnd01() < 0.7) ? lo + rndint(40) : lo + rndint(span);
        int ok = 0;
        for (int t = 0; t < 300 && !ok; t++) ok = sample_desc(N, &ds);
        if (!ok) {
            if (++spins > 200000) break;
            continue;
        }
        build_group(&ds);
        if (!search_group(g)) continue;
        if (make_candidate(g) && cand.n > best.n) {
            memcpy(&best, &cand, sizeof(Graph));
            lo = best.n / 2 + 1;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    need_n = argc >= 6 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start();
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    init_bases();
    if (best.n < moore_bipartite()) search();
    print_graph(&best);
    return 0;
}
'''

RECORDS = {(3, 3): 14, (4, 7): 840}


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
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, degree 4, diameter 6."""
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), RECORDS.get((d, D), 0)],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
