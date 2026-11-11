"""Bipartite voltage-lift search over fixed small bases, with a safe fallback.

Idea (new in this version): instead of growing a bi-Cayley graph from two fibres, start from a
small algebraic bipartite base with large spare structure (the W(q) quadrangle incidence graph
and the PG(2,q) plane incidence graph, plus K_{d,d}). Choose a metacyclic group of order N, give
each base edge a random voltage, and anneal the voltages so every base vertex reaches all
vertices within D. A lift has base_n * N vertices and keeps the base degree and bipartition.
Diameter is checked exactly: left multiplication is an automorphism acting regularly on each
fibre, so BFS from the identity of each base fibre suffices.

The C engine tries the smallest order N with base_n * N above the current best, and keeps
increasing N after each success. Python keeps the best valid graph among the algebraic
fallbacks and the lift results, and validates every returned graph with lib.is_valid.
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

#define MAXN 8192
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXBN 256
#define MAXE (MAXBN * MAXD / 2)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int d, D;
static long MOORE;
static double t_stop;

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

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static void set_group(Grp *G, int m, int k, int r) {
    G->m = m; G->k = k; G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random metacyclic group of order N (reservoir sampling over all (m, r)). */
static int pick_group(int N, Grp *G) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            count++;
            if (rndint((int)count) == 0) { bm = 1; bk = k; br = 1; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (count == 0) return 0;
    set_group(G, bm, bk, br);
    return 1;
}

/* ---- base graph (bipartite, max degree <= d, simple) ---- */
static int bn, ne;
static int bside[MAXBN];
static int ea[MAXE], eb[MAXE];   /* ea in side 0, eb in side 1 */
static int dg[MAXE];             /* voltage of each base edge */

static int read_base(void) {
    int m;
    if (scanf("%d %d", &bn, &m) != 2) return 0;
    if (bn <= 0 || bn > MAXBN || m <= 0 || m > MAXE) return 0;
    static unsigned char am[MAXBN][MAXBN];
    static int eu[MAXE], ev[MAXE];
    static int st[MAXBN];
    int bdeg[MAXBN];
    memset(am, 0, sizeof am);
    for (int v = 0; v < bn; v++) { bdeg[v] = 0; bside[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= bn || v >= bn || u == v || am[u][v]) return 0;
        am[u][v] = am[v][u] = 1;
        eu[e] = u; ev[e] = v;
        bdeg[u]++; bdeg[v]++;
    }
    for (int v = 0; v < bn; v++) if (bdeg[v] > d) return 0;
    for (int s = 0; s < bn; s++) {
        if (bside[s] != -1) continue;
        int sp = 0;
        bside[s] = 0;
        st[sp++] = s;
        while (sp > 0) {
            int v = st[--sp];
            for (int u = 0; u < bn; u++) {
                if (!am[v][u]) continue;
                if (bside[u] == -1) { bside[u] = 1 - bside[v]; st[sp++] = u; }
                else if (bside[u] == bside[v]) return 0;
            }
        }
    }
    ne = m;
    for (int e = 0; e < m; e++) {
        if (bside[eu[e]] == 0) { ea[e] = eu[e]; eb[e] = ev[e]; }
        else { ea[e] = ev[e]; eb[e] = eu[e]; }
    }
    return 1;
}

/* ---- lift ---- */
static Graph lift, best;
static Grp G;
static int curN;
static int have_best = 0;

/* Vertex (a, x) has index a*N + x; edge t joins (ea,x) to (eb, x*g_t). */
static void build_lift(void) {
    int N = curN, V = bn * N;
    lift.n = V;
    for (int v = 0; v < V; v++) {
        lift.deg[v] = 0;
        lift.side[v] = (unsigned char)bside[v / N];
    }
    for (int t = 0; t < ne; t++)
        for (int x = 0; x < N; x++)
            add_edge(&lift, ea[t] * N + x, eb[t] * N + gmul(&G, x, dg[t]));
}

static int dist_a[MAXN], q_a[MAXN], stampv[MAXN];
static int stamp_c = 0;

/* Sum over base fibres of the number of vertices NOT reached within D from the fibre identity. */
static long orbit_bad(void) {
    int V = lift.n, N = curN;
    long total = 0;
    for (int a = 0; a < bn; a++) {
        int src = a * N;
        stamp_c++;
        int head = 0, tail = 0;
        stampv[src] = stamp_c;
        dist_a[src] = 0;
        q_a[tail++] = src;
        while (head < tail && tail < V) {
            int v = q_a[head++];
            if (dist_a[v] >= D) continue;
            for (int i = 0; i < lift.deg[v]; i++) {
                int u = lift.adj[v][i];
                if (stampv[u] != stamp_c) {
                    stampv[u] = stamp_c;
                    dist_a[u] = dist_a[v] + 1;
                    q_a[tail++] = u;
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static long anneal(double until) {
    build_lift();
    long bad = orbit_bad();
    double T = 3.0;
    for (long it = 0; bad > 0; it++) {
        if ((it & 15) == 0 && now() > until) break;
        int t = rndint(ne);
        int old = dg[t];
        int ng = rndint(curN);
        if (ng == old) continue;
        dg[t] = ng;
        build_lift();
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.3) T = 3.0;
    }
    build_lift();
    return bad;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n] < base_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long min_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_stop = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    MOORE = moore_bound();
    if (d < 1 || d > MAXD || D < 1 || !read_base()) {
        printf("0 0\n");
        return 0;
    }

    long N = min_n / bn + 1;
    while (now() < t_stop) {
        if ((long)bn * N > MOORE || (long)bn * N > MAXN) break;
        double left = t_stop - now();
        if (left < 0.2) break;
        double sl = left * 0.5;
        if (!pick_group((int)N, &G)) { N++; continue; }
        curN = (int)N;
        for (int t = 0; t < ne; t++) dg[t] = rndint((int)N);
        long bad = anneal(now() + sl);
        if (bad == 0) {
            build_lift();
            if (is_valid(&lift)) {
                copy_graph(&best, &lift);
                have_best = 1;
                N++;
            }
        }
    }

    if (have_best) print_graph(&best);
    else printf("0 0\n");
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
        q = _largest_prime_power_le(min(d - 1, 7))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def bases(d, D):
    """Bipartite, max-degree-d base graphs for voltage lifts, most promising first."""
    out = []
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        if D >= 4 and q <= 7:
            out.append(_gq_w(q))
        if D >= 3:
            out.append(lib.projective_plane_incidence(q))
    out.append(lib.haar_graph(d, range(d)))  # K_{d,d}
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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget_total = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget_total <= 1.0:
        return best

    bl = bases(d, D)[:2]
    for i, base in enumerate(bl):
        left = budget_total - (time.monotonic() - t0)
        b = left / (len(bl) - i)
        if b < 1.0:
            break
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed + i, round(b, 2), best[0]],
                             stdin_graph=base, timeout=b + 4)
            n, e = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass
    return best
