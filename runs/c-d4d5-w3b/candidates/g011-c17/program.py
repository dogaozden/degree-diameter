"""Group-lift annealing program: Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez,
or K_{d,d}) and checks it with lib.is_valid. The C engine then searches over semidirect-product voltage
lifts of many group orders, with simulated annealing on the voltages. Any accepted lift that beats the
current best is saturated and checked with a full bitset diameter test before it is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Group-lift annealing search for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Lifts: base multigraph on p+p vertices (p in 1..4), d-regular, with voltages in the
 * semidirect product Z_m x|_r Z_k (order N). Vertex (i,x) joins (p+j, x*g) for each dart (i,j,g).
 * Left multiplication is an automorphism, so the diameter test only needs BFS from the 2p
 * fibre representatives. Voltages are annealed to remove all pairs at distance > D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXW (MAXV / 64)
#define MAXDEG 40
#define MAXP 4
#define MAXG 1024

static int d, D;
static long moore;

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

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXDEG];
} Graph;

static void gadd(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

static int simple_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
            int back = 0;
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == v) { back = 1; break; }
            if (!back) return 0;
        }
    }
    return 1;
}

static int colr[MAXV];
/* Fills colr with a 2-colouring; returns 1 if the graph is bipartite. */
static int colour(const Graph *g) {
    static int q[MAXV];
    int n = g->n;
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (colr[u] < 0) {
                    colr[u] = 1 - colr[v];
                    q[t++] = u;
                } else if (colr[u] == colr[v]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static uint64_t BA[MAXV * MAXW], BB[MAXV * MAXW];

/* Number of unordered pairs at distance > D, by bitset expansion. */
static long full_bad(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
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

static int graph_valid(const Graph *g) {
    if (!simple_ok(g)) return 0;
    if (!colour(g)) return 0;
    return full_bad(g) == 0;
}

/* Greedy addition of missing A-B edges between vertices with spare degree.
 * Adding such an edge never increases a distance, so validity is kept. */
static int saturate(Graph *g) {
    if (!colour(g)) return 0;
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (colr[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (colr[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            gadd(g, a, b);
            added++;
        }
    }
    return added;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) g->deg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { g->n = 0; return; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { g->n = 0; return; }
        if (g->deg[u] >= MAXDEG - 1 || g->deg[v] >= MAXDEG - 1) { g->n = 0; return; }
        if (has_edge(g, u, v)) { g->n = 0; return; }
        gadd(g, u, v);
    }
    if (!graph_valid(g)) g->n = 0;
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
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) gadd(g, a, d + b);
}

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
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

/* Semidirect products Z_m x|_r Z_k with m*k = N, gcd(r,m)=1, r^k = 1 mod m. */
typedef struct {
    int m, k, r;
    int rp[MAXG];
} Grp;

static void setup_group(Grp *G, int m, int k, int r) {
    G->m = m;
    G->k = k;
    G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int gmul(const Grp *G, int x, int y) {
    int k = G->k, m = G->m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int aa = (int)(((long)a + (long)G->rp[b] * c) % m);
    return aa * k + (b + e) % k;
}

static int list_groups(int N, int (*out)[3]) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcdi(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt >= MAXG) return cnt;
            out[cnt][0] = m;
            out[cnt][1] = k;
            out[cnt][2] = r;
            cnt++;
        }
    }
    return cnt;
}

typedef struct { int i, j, g; } Dart;

static int MB[MAXP][MAXP];

/* Random d-regular connected bipartite base multigraph on p + p vertices. */
static void make_base(int p) {
    for (;;) {
        memset(MB, 0, sizeof MB);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) MB[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && MB[v][u - p] > 0) : (u < p && MB[u][v - p] > 0);
                if (linked) {
                    seen[u] = 1;
                    ns++;
                    st[top++] = u;
                }
            }
        }
        if (ns == 2 * p) return;
    }
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) g->deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            gadd(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_[MAXV], qu_[MAXV];

/* Sum over the 2p fibre representatives of the number of vertices at distance > D. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[src] = 0;
        qu_[t++] = src;
        while (h < t) {
            int v = qu_[h++];
            if (dist_[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    qu_[t++] = u;
                }
            }
        }
        total += nv - t;
    }
    return total;
}

/* Anneal the voltages of one random base over the group G until the lift has diameter <= D. */
static int anneal_lift(Graph *g, int p, int N, const Grp *G, Dart *dt, int *ndp,
                       int steps, double until) {
    make_base(p);
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < MB[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    *ndp = nd;
    build_lift(g, p, N, G, dt, nd);
    long bad = orbit_bad(g, p, N);
    double T = 0.8;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) bad = nb;
        else dt[t].g = old;
        T *= 0.9995;
        if (T < 0.05) T = 0.8;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

static void search(Graph *best, double until) {
    static Graph cand;
    static Dart dt[MAXDEG * MAXP];
    static int grp[MAXG][3];
    static Grp G;
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        int p = 1 + rndint(MAXP);
        long Nmin = (target + 2L * p - 1) / (2L * p);
        long N = Nmin + rndint(6);
        if (N < d + 1) N = d + 1;
        if (2L * p * N > moore || 2L * p * N > MAXV || N >= MAXG) continue;
        int cnt = list_groups((int)N, grp);
        if (cnt == 0) continue;
        int pick = rndint(cnt);
        setup_group(&G, grp[pick][0], grp[pick][1], grp[pick][2]);
        int ok = 0;
        for (int a = 0; a < 3 && !ok && now() < until; a++) {
            int nd = 0;
            if (anneal_lift(&cand, p, (int)N, &G, dt, &nd, 5000, until)) {
                saturate(&cand);
                if (cand.n > best->n && graph_valid(&cand)) {
                    *best = cand;
                    ok = 1;
                }
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
    double t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 2 || d > MAXDEG - 4) {
        printf("0 0\n");
        return 0;
    }
    moore = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!graph_valid(&best)) complete_bipartite(&best);
    if (best.n < moore) search(&best, t_end);
    if (!graph_valid(&best)) complete_bipartite(&best);
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
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
