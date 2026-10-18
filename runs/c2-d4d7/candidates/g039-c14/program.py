"""Bi-Cayley (Haar-type) search over finite groups, with the parent's Python constructions kept as the fallback.

Change from the parent: the C engine no longer hill-climbs covers or random voltage lifts. It searches
Haar graphs H(G, S): vertices a_x and b_y (x, y in G), with a_x adjacent to b_{x s} for s in S, |S| = d.
Left multiplication by G is an automorphism, so the diameter test reduces to two BFS runs, from a_e and b_e.
The groups are direct products X x Z_k, where X is PSL(2,p), PGL(2,p) for p in {5, 7, 11}, or PSL(2,8)
(order 504, so the graph has 1008 vertices, above the record 840). Other groups are metacyclic Z_m x| Z_k,
which include cyclic and abelian groups. The connection set is annealed directly, with identity fixed in S
by right-translation normalisation. Groups are scheduled round-robin with doubling budgets.
Python keeps the algebraic starts (PG(2,q), W(q), H(3)) and validates every output. Any failure falls
back to the best valid graph found so far.
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

#define MAXN 2304
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 1400
#define HS 8192
#define NXG 6
#define POOL_X 64
#define POOL_TOT 180

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int type, xi, m, k, r, N; } Desc;
typedef struct { unsigned char p[16]; } Perm;

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance greater than D. */
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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

/* ---------------------------------------------------------------- permutation groups */
static int XO[NXG];
static int *XT[NXG], *XI[NXG];

static Perm ELEM[MAXG];
static uint64_t hkey[HS];
static int hval[HS];

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

/* Closure of generators on s points; ELEM[0] is the identity. */
static int closure_gens(const Perm *gens, int ng, int s, int *ordp) {
    memset(hval, 0, sizeof hval);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gens[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *ordp = n;
    return 1;
}

static int build_X(int xi, const Perm *gens, int ng, int s) {
    int o = 0;
    if (!closure_gens(gens, ng, s, &o)) return 0;
    int *mt = malloc(sizeof(int) * (size_t)o * (size_t)o);
    int *iv = malloc(sizeof(int) * (size_t)o);
    if (!mt || !iv) return 0;
    for (int i = 0; i < o; i++)
        for (int j = 0; j < o; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            mt[(size_t)i * o + j] = idx < 0 ? 0 : idx;
        }
    for (int i = 0; i < o; i++) {
        iv[i] = 0;
        for (int j = 0; j < o; j++)
            if (mt[(size_t)i * o + j] == 0) { iv[i] = j; break; }
    }
    XT[xi] = mt;
    XI[xi] = iv;
    XO[xi] = o;
    return 1;
}

/* PSL(2,p) or PGL(2,p) acting on the p+1 points of the projective line. */
static void make_psl(int p, int pgl, int xi) {
    Perm g[3];
    memset(g, 0, sizeof g);
    int s = p + 1, inf = p, prim = 1, ng = 0;
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++) g[0].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng = 1;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        g[1].p[x] = (unsigned char)v;
    }
    ng = 2;
    if (pgl) {
        for (int x = 0; x <= p; x++) g[2].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng = 3;
    }
    build_X(xi, g, ng, s);
}

static int gf8mul(int a, int b) {
    int r = 0;
    for (int i = 0; i < 3; i++)
        if ((b >> i) & 1) r ^= a << i;
    for (int i = 4; i >= 3; i--)
        if ((r >> i) & 1) r ^= 0xB << (i - 3);
    return r;
}

static int gf8inv(int x) {
    for (int y = 1; y < 8; y++)
        if (gf8mul(x, y) == 1) return y;
    return 0;
}

/* PSL(2,8) on the 9 points of the projective line over GF(8). */
static void make_psl8(int xi) {
    Perm g[3];
    memset(g, 0, sizeof g);
    for (int x = 0; x < 8; x++) {
        g[0].p[x] = (unsigned char)(x ^ 1);
        g[1].p[x] = (unsigned char)gf8mul(2, x);
    }
    g[0].p[8] = 8;
    g[1].p[8] = 8;
    g[2].p[0] = 8;
    g[2].p[8] = 0;
    for (int x = 1; x < 8; x++) g[2].p[x] = (unsigned char)gf8inv(x);
    build_X(xi, g, 3, 9);
}

static void init_groups(void) {
    make_psl(5, 0, 0);
    make_psl(5, 1, 1);
    make_psl(7, 0, 2);
    make_psl(7, 1, 3);
    make_psl8(4);
    make_psl(11, 0, 5);
}

/* ---------------------------------------------------------------- group arithmetic */
static Desc CUR;
static int NN;
static int RP[MAXG];

static void set_group(const Desc *dsc) {
    CUR = *dsc;
    NN = CUR.N;
    if (CUR.type == 0) {
        int m = CUR.m, k = CUR.k;
        if (m == 1) {
            for (int b = 0; b < k; b++) RP[b] = 0;
        } else {
            RP[0] = 1 % m;
            for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * CUR.r % m);
        }
    }
}

static int gmul(int x, int y) {
    if (CUR.type == 0) {
        int k = CUR.k, m = CUR.m;
        int a = x / k, b = x % k, c = y / k, e = y % k;
        return (int)(((a + (long)RP[b] * c) % m) * k + (b + e) % k);
    } else {
        int k = CUR.k, o = XO[CUR.xi];
        int x1 = x / k, c1 = x % k, y1 = y / k, c2 = y % k;
        return XT[CUR.xi][x1 * o + y1] * k + (c1 + c2) % k;
    }
}

static int ginv(int x) {
    if (CUR.type == 0) {
        int k = CUR.k, m = CUR.m;
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int na = (int)((m - (long)RP[nb] * a % m) % m);
        return na * k + nb;
    } else {
        int k = CUR.k;
        int x1 = x / k, c1 = x % k;
        return XI[CUR.xi][x1] * k + (k - c1) % k;
    }
}

/* ---------------------------------------------------------------- Haar graph search */
static int S[MAXD];
static int Rr[MAXD][MAXG], Ll[MAXD][MAXG];
static int vis[2 * MAXG], dd[2 * MAXG], qb[2 * MAXG];
static int vstamp = 0;

static void update_row(int i) {
    int si = S[i], sinv = ginv(si);
    for (int x = 0; x < NN; x++) {
        Rr[i][x] = gmul(x, si);
        Ll[i][x] = gmul(x, sinv);
    }
}

/* Vertices 0..NN-1 are a-vertices, NN..2NN-1 are b-vertices. Returns the number of vertices
 * not within distance D of src. */
static long unreached(int src) {
    int N = NN;
    int head = 0, tail = 0;
    vstamp++;
    qb[tail++] = src;
    vis[src] = vstamp;
    dd[src] = 0;
    while (head < tail) {
        int v = qb[head++];
        int dv = dd[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + Rr[i][v];
                if (vis[u] != vstamp) { vis[u] = vstamp; dd[u] = dv + 1; qb[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = Ll[i][y];
                if (vis[u] != vstamp) { vis[u] = vstamp; dd[u] = dv + 1; qb[tail++] = u; }
            }
        }
    }
    return 2L * N - tail;
}

static long cost(void) {
    return unreached(0) + unreached(NN);
}

static int in_S(int g, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == g) return 1;
    return 0;
}

/* Simulated annealing over connection sets S (identity fixed in S[0]) for the current group. */
static int sa_group(long E) {
    int N = NN;
    if (N <= d) return 0;
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_S(g, i));
        S[i] = g;
    }
    for (int i = 0; i < d; i++) update_row(i);
    long cur = cost();
    if (cur == 0) return 1;
    const double T0 = 3.0, T1 = 0.2;
    for (long t = 0; t < E; t++) {
        if ((t & 63) == 0 && now() > t_end) return 0;
        int i = 1 + rndint(d - 1);
        int g;
        do { g = rndint(N); } while (in_S(g, d));
        int old = S[i];
        S[i] = g;
        update_row(i);
        double T = T0 * pow(T1 / T0, (double)t / (double)E);
        long nw = cost();
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            S[i] = old;
            update_row(i);
        }
    }
    return 0;
}

static Desc pool[POOL_TOT];
static int npool;

static void pool_meta_add(int base, int cap, int *filled, int *seen,
                          int m, int k, int r, int N) {
    Desc x = {0, 0, m, k, r, N};
    (*seen)++;
    if (*filled < cap) {
        pool[base + *filled] = x;
        (*filled)++;
    } else {
        int j = rndint(*seen);
        if (j < cap) pool[base + j] = x;
    }
}

static void build_pool(int lo, int hi) {
    npool = 0;
    for (int xi = 0; xi < NXG; xi++) {
        int o = XO[xi];
        if (!o) continue;
        for (int k = 1; o * k <= hi; k++) {
            int N = o * k;
            if (N < lo || N <= d || npool >= POOL_X) continue;
            Desc x = {1, xi, 0, k, 0, N};
            pool[npool++] = x;
        }
    }
    int base = npool, cap = POOL_TOT - base, filled = 0, seen = 0;
    for (int N = lo; N <= hi; N++) {
        if (N <= d) continue;
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                pool_meta_add(base, cap, &filled, &seen, 1, k, 0, N);
            } else {
                for (int r = 1; r < m; r++) {
                    if (gcd(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1) continue;
                    pool_meta_add(base, cap, &filled, &seen, m, k, r, N);
                }
            }
        }
    }
    /* Metacyclic entries are stored with type 0; fix the type field now. */
    for (int i = base; i < base + filled; i++) pool[i].type = 0;
    npool = base + filled;
}

static Desc BestDesc;
static int BestS[MAXD];
static int BestN;

static int search_haar(int start_n) {
    long moore = moore_bound();
    long hi = moore / 2;
    if (hi > MAXN / 2) hi = MAXN / 2;
    if (hi > MAXG) hi = MAXG;
    int best_N = start_n / 2;
    int have = 0;
    while (now() < t_end) {
        long lo = best_N + 1;
        if (lo > hi) break;
        build_pool((int)lo, (int)hi);
        if (npool == 0) break;
        int improved = 0;
        for (long E = 400; !improved && now() < t_end; E *= 2) {
            for (int p = 0; p < npool && now() < t_end; p++) {
                set_group(&pool[p]);
                if (sa_group(E)) {
                    improved = 1;
                    have = 1;
                    best_N = NN;
                    BestN = NN;
                    BestDesc = pool[p];
                    memcpy(BestS, S, sizeof S);
                    break;
                }
            }
        }
        if (!improved) break;
    }
    return have;
}

static void build_haar(Graph *g) {
    int N = NN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= N);
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + Rr[i][x]);
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
    t_end = t0 + limit * 0.90;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        Graph triv;
        d = 1;
        triv.n = 2;
        triv.deg[0] = triv.deg[1] = 0;
        triv.side[0] = 0;
        triv.side[1] = 1;
        add_edge(&triv, 0, 1);
        print_graph(&triv);
        return 0;
    }

    static Graph start, gout;
    read_start(&start);
    if (start.n == 0) complete_bipartite(&start);

    int have = 0;
    if (d >= 3 && D >= 2 && start.n < moore_bound()) {
        init_groups();
        have = search_haar(start.n);
    }
    if (have) {
        set_group(&BestDesc);
        NN = BestN;
        for (int i = 0; i < d; i++) S[i] = BestS[i];
        for (int i = 0; i < d; i++) update_row(i);
        build_haar(&gout);
        if (gout.n > start.n && is_valid(&gout)) {
            print_graph(&gout);
            return 0;
        }
    }
    print_graph(&start);
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

    # The C engine reads its start graph with at most 2304 vertices, and the Moore bound
    # rules out any gain once the start already meets it.
    if d > 31 or best[0] >= lib.moore_bound(d, D) or best[0] > 2000:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
