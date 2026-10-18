"""Bi-Cayley (Haar-type) search over explicit permutation groups, for the weakest target (d=4, D=7).

Change from the parent: the main search is no longer voltage lifts over small base graphs. C now runs
simulated annealing over connection sets S of Haar graphs H(G, S): a_x ~ b_{x s} for s in S, with |S| = d
and the identity fixed in S (right-translation normalisation). G is supplied as permutation generators
(PSL, PGL and PGammaL(2,q) on the projective line, direct products with cyclic groups, S6, affine groups
Z_p x| Z_k), and the C engine builds the multiplication tables itself. Left-regular action makes the
diameter test two BFS runs (from a_e and b_e). Found graphs are grown by two vertices with annealing.
Every output is checked by lib.is_valid, and the Python fallbacks (algebraic starts, K_{d,d}) are kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley (Haar graph) annealing over permutation groups, then grow-by-two.
 * Usage:  prog d D seed time_limit [floor]
 * stdin:  "NG m" header, then NG groups as "P ng" followed by ng permutations of P points.
 *         (the stream may be laid out in pairs; only the integer order matters)
 * stdout: "n m" then m lines "u v": the largest valid graph found (K_{d,d} if none).
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
#define MAXG 1600
#define MAXSN 1000
#define MAXP 40
#define MAXGEN 6
#define MAXNG 64
#define HS 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static int floor_n = 0;
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

/* ---------------------------------------------------------------- groups */
typedef struct {
    int N, P, ng;
    int built;                       /* 0 = not built, 1 = ready, -1 = unusable */
    unsigned char gen[MAXGEN][MAXP];
    unsigned short *gt;              /* gt[x*N+y] = x*y, identity index 0 */
    int *inv;
} Group;

static Group GR[MAXNG];
static int nGroups = 0;

static void read_groups(void) {
    int total = 0, m_hdr = 0;
    nGroups = 0;
    if (scanf("%d %d", &total, &m_hdr) != 2) return;
    for (int g = 0; g < total; g++) {
        int P, ng;
        if (scanf("%d %d", &P, &ng) != 2) return;
        if (P < 1 || P > MAXP || ng < 1 || ng > MAXGEN) return;
        unsigned char tmp[MAXGEN][MAXP];
        int ok = 1;
        for (int k = 0; k < ng; k++) {
            int seen[MAXP];
            memset(seen, 0, sizeof seen);
            for (int i = 0; i < P; i++) {
                int v;
                if (scanf("%d", &v) != 1) return;
                if (v < 0 || v >= P || seen[v]) ok = 0;
                else { seen[v] = 1; tmp[k][i] = (unsigned char)v; }
            }
        }
        if (ok && nGroups < MAXNG) {
            Group *G = &GR[nGroups++];
            G->P = P;
            G->ng = ng;
            G->built = 0;
            G->N = 0;
            G->gt = NULL;
            G->inv = NULL;
            memcpy(G->gen, tmp, sizeof tmp);
        }
    }
}

static unsigned char ELEM[MAXG][MAXP];
static int HT[HS];

static uint64_t fnv(const unsigned char *p, int P) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < P; i++) {
        h ^= p[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static unsigned hslot(const unsigned char *p, int P) {
    return (unsigned)(fnv(p, P) & (HS - 1));
}

static int ht_find(const unsigned char *p, int P) {
    unsigned s = hslot(p, P);
    while (HT[s]) {
        if (memcmp(ELEM[HT[s] - 1], p, (size_t)P) == 0) return HT[s] - 1;
        s = (s + 1) & (HS - 1);
    }
    return -1;
}

static void ht_put(const unsigned char *p, int P, int idx) {
    unsigned s = hslot(p, P);
    while (HT[s]) s = (s + 1) & (HS - 1);
    HT[s] = idx + 1;
}

/* Closure of the generators, then the full multiplication table. */
static int build_group(Group *G) {
    int P = G->P, n = 1;
    unsigned char h[MAXP];
    memset(HT, 0, sizeof HT);
    for (int i = 0; i < P; i++) ELEM[0][i] = (unsigned char)i;
    ht_put(ELEM[0], P, 0);
    for (int q = 0; q < n; q++)
        for (int k = 0; k < G->ng; k++) {
            for (int i = 0; i < P; i++) h[i] = ELEM[q][G->gen[k][i]];
            if (ht_find(h, P) < 0) {
                if (n >= MAXG) return 0;
                memcpy(ELEM[n], h, (size_t)P);
                ht_put(h, P, n);
                n++;
            }
        }
    unsigned short *gt = malloc(sizeof(unsigned short) * (size_t)n * (size_t)n);
    int *inv = malloc(sizeof(int) * (size_t)n);
    if (!gt || !inv) { free(gt); free(inv); return 0; }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++) {
            for (int i = 0; i < P; i++) h[i] = ELEM[x][ELEM[y][i]];
            int idx = ht_find(h, P);
            if (idx < 0) { free(gt); free(inv); return 0; }
            gt[(size_t)x * n + y] = (unsigned short)idx;
        }
    for (int x = 0; x < n; x++) inv[x] = 0;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (gt[(size_t)x * n + y] == 0) inv[x] = y;
    G->N = n;
    G->gt = gt;
    G->inv = inv;
    return 1;
}

/* ---------------------------------------------------------------- Haar annealing
 * H(G,S): a_x ~ b_{x s}, s in S. Left-regular action: dist(a_x, a_y) depends on x^-1 y,
 * and the same holds for b. A valid graph needs every vertex within D of a_e and of b_e. */
static int SN;
static const unsigned short *SGT;
static const int *SINV;
static int vis[2 * MAXG];
static int vstamp = 0;
static int bq[2 * MAXG];

static long miss_from(int src, const int *S, const int *IS, int dd) {
    int N = SN, tot = 2 * N;
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    bq[tail++] = src;
    int level_end = 1;
    for (int lvl = 0; lvl < D && tail < tot; lvl++) {
        while (head < level_end) {
            int v = bq[head++];
            if (v < N) {
                const unsigned short *row = SGT + (size_t)v * N;
                for (int i = 0; i < dd; i++) {
                    int u = N + row[S[i]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; bq[tail++] = u; }
                }
            } else {
                const unsigned short *row = SGT + (size_t)(v - N) * N;
                for (int i = 0; i < dd; i++) {
                    int u = row[IS[i]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; bq[tail++] = u; }
                }
            }
        }
        level_end = tail;
    }
    return tot - tail;
}

static long haar_cost(const int *S, int dd) {
    int IS[MAXD];
    for (int i = 0; i < dd; i++) IS[i] = SINV[S[i]];
    return miss_from(0, S, IS, dd) + miss_from(SN, S, IS, dd);
}

static int contains(const int *S, int cnt, int x) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing on S = {0, s_1, ..., s_{d-1}}. Returns 1 and writes S if cost reaches 0. */
static int sa_group(const Group *G, double until, int *outS) {
    int N = G->N, dd = d;
    SN = N;
    SGT = G->gt;
    SINV = G->inv;
    int S[MAXD], bestS[MAXD];
    S[0] = 0;
    for (int i = 1; i < dd; i++) {
        int x;
        do { x = 1 + rndint(N - 1); } while (contains(S, i, x));
        S[i] = x;
    }
    long c = haar_cost(S, dd), bestc = c;
    memcpy(bestS, S, sizeof(int) * dd);
    double T = 3.0;
    for (long it = 1; bestc > 0; it++) {
        if ((it & 127) == 0 && now() > until) break;
        int i = 1 + rndint(dd - 1);
        int x;
        do { x = 1 + rndint(N - 1); } while (contains(S, dd, x));
        int old = S[i];
        S[i] = x;
        long c2 = haar_cost(S, dd);
        if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
            c = c2;
            if (c < bestc) {
                bestc = c;
                memcpy(bestS, S, sizeof(int) * dd);
            }
        } else {
            S[i] = old;
        }
        T *= 0.9995;
        if (T < 0.5) T = 3.0;
    }
    if (bestc != 0) return 0;
    memcpy(outS, bestS, sizeof(int) * dd);
    return 1;
}

static void build_haar(Graph *g, const Group *G, const int *S) {
    int N = G->N;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= N);
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + G->gt[(size_t)x * N + S[i]]);
}

static void haar_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    for (int round = 0; now() < until; round++) {
        double slice = 0.4 * (double)(1 << (round < 6 ? round : 6));
        int any = 0;
        for (int gi = 0; gi < nGroups && now() < until; gi++) {
            Group *G = &GR[gi];
            if (G->built == 0) G->built = build_group(G) ? 1 : -1;
            if (G->built != 1) continue;
            int need = best->n > floor_n ? best->n : floor_n;
            if (2L * G->N <= need || 2L * G->N > moore || G->N > MAXSN || G->N <= d + 1) continue;
            any = 1;
            double ug = now() + slice;
            if (ug > until) ug = until;
            int S[MAXD];
            if (sa_group(G, ug, S)) {
                build_haar(&cand, G, S);
                if (cand.n > need && is_valid(&cand)) copy_graph(best, &cand);
            }
        }
        if (!any) break;
    }
}

/* ---------------------------------------------------------------- grow by two */
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
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
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
        fprintf(stderr, "usage: %s d D seed time_limit [floor] < groups\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    floor_n = argc >= 6 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_groups();
    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static Graph best;
    complete_bipartite(&best);
    if (best.n < moore_bound()) {
        haar_search(&best, t0 + (t_end - t0) * 0.65);
        if (best.n > floor_n && best.n < moore_bound()) grow_search(&best, t_end);
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

    Returns None if no sign convention yields a graph that passes lib.is_valid.
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


# ------------------------------------------------ permutation groups for the C engine

def _line_group(q, kind):
    """(M, gens): permutations of P^1(F_q) = {0..q-1, inf=q} generating PSL, PGL or PGammaL(2,q)."""
    F = lib.GF(q)
    M = q + 1
    inf = q
    w = F.primitive_element()
    t = [F.add(x, 1) for x in range(q)] + [inf]                 # x -> x + 1
    mulg = F.mul(w, w) if kind == "PSL" else w                  # x -> a x
    m = [F.mul(mulg, x) for x in range(q)] + [inf]
    s = [inf] + [F.neg(F.inv(x)) for x in range(1, q)] + [0]    # x -> -1/x
    gens = [t, m, s]
    if kind == "PGammaL":
        gens.append([F.pow(x, F.p) for x in range(q)] + [inf])  # field automorphism
    return M, gens


def _extend_cyclic(M, gens, k):
    """Direct product with Z_k acting as a k-cycle on k extra points."""
    P = M + k
    ext = [list(g) + list(range(M, P)) for g in gens]
    ext.append(list(range(M)) + [M + (i + 1) % k for i in range(k)])
    return P, ext


def _primitive_root(p):
    fs = [f for f in range(2, p) if (p - 1) % f == 0 and all(f % j for j in range(2, f))]
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    raise ValueError("no primitive root")


def _affine_specs():
    """Z_p x| Z_k acting on p points, x -> x + 1 and x -> r x with r of order k."""
    out = []
    for p in (17, 19, 23, 29, 31, 37):
        g = _primitive_root(p)
        for k in range(2, p):
            if (p - 1) % k == 0 and 300 <= p * k <= 1100:
                r = pow(g, (p - 1) // k, p)
                out.append((p, [[(x + 1) % p for x in range(p)],
                                [(r * x) % p for x in range(p)]]))
    return out


def _group_specs():
    specs = []
    for q, kinds in ((7, ("PSL", "PGL")), (8, ("PSL", "PGammaL")),
                     (9, ("PSL", "PGL", "PGammaL")), (11, ("PSL", "PGL")), (13, ("PSL",))):
        for kind in kinds:
            specs.append(_line_group(q, kind))
    for q, kind, ks in ((7, "PSL", (2, 3, 4, 5, 6)), (7, "PGL", (2, 3)),
                        (8, "PSL", (2,)), (9, "PSL", (2, 3)), (11, "PSL", (2,))):
        M, g = _line_group(q, kind)
        for k in ks:
            specs.append(_extend_cyclic(M, g, k))
    specs.append((6, [[1, 0, 2, 3, 4, 5], [1, 2, 3, 4, 5, 0]]))  # S6
    specs += _affine_specs()
    return specs


def _encode_groups(specs):
    """(NG, pairs): the flat integer stream of the groups, packed into pairs for lib.graph_to_text."""
    flat = []
    for P, gens in specs:
        flat += [P, len(gens)]
        for g in gens:
            flat += list(g)
    if len(flat) % 2:
        flat.append(0)
    pairs = [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)]
    return len(specs), pairs


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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 2.0:
        return best
    try:
        ng, pairs = _encode_groups(_group_specs())
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0]],
                         stdin_graph=(ng, pairs), timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
