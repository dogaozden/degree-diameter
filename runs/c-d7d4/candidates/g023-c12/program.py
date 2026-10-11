import itertools

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXDEG 32
#define WMAX 22

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXDEG];
} Graph;

static Graph G, BEST;
static int dd, DD;
static int have_best = 0;
static uint64_t rs = 88172645463325252ULL;
static uint64_t bufA[MAXN][WMAX], bufB[MAXN][WMAX];
static clock_t T0;
static int sw_a, sw_b, sw_c, sw_e;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double elapsed(void) {
    return (double)(clock() - T0) / CLOCKS_PER_SEC;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) return 1;
    return 0;
}

static void arc_del(Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->adj[a][i] == b) {
            g->adj[a][i] = g->adj[a][g->deg[a] - 1];
            g->deg[a]--;
            return;
        }
    }
}

static void edge_del(Graph *g, int a, int b) {
    arc_del(g, a, b);
    arc_del(g, b, a);
}

static void edge_add(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

/* Number of unordered pairs at distance greater than DD (unreachable counts). */
static long long bad_pairs(const Graph *g) {
    int n = g->n;
    int nw = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                for (int w = 0; w < nw; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Bipartite double edge switch: a-b, c-e  ->  a-e, c-b (degrees kept). */
static int switch_move(Graph *g) {
    int n = g->n;
    int a = rndint(n);
    if (g->deg[a] == 0) return 0;
    int b = g->adj[a][rndint(g->deg[a])];
    int c = rndint(n);
    if (c == a || g->col[c] != g->col[a] || g->deg[c] == 0) return 0;
    int e = g->adj[c][rndint(g->deg[c])];
    if (has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    edge_del(g, a, b);
    edge_del(g, c, e);
    edge_add(g, a, e);
    edge_add(g, c, b);
    sw_a = a; sw_b = b; sw_c = c; sw_e = e;
    return 1;
}

static void switch_undo(Graph *g) {
    edge_del(g, sw_a, sw_e);
    edge_del(g, sw_c, sw_b);
    edge_add(g, sw_a, sw_b);
    edge_add(g, sw_c, sw_e);
}

/* Pair insertion: new v (side c) joined to X, new w (side 1-c) joined to Y,
   where each X[i]-Y[i] was an edge that is removed. Degrees are preserved. */
static int grow_move(Graph *g) {
    int n = g->n;
    if (n + 2 > MAXN) return 0;
    int c = rndint(2);
    int X[MAXDEG], Y[MAXDEG];
    int k = 0;
    for (int tries = 0; k < dd && tries < 4000; tries++) {
        int x = rndint(n);
        if (g->col[x] == c || g->deg[x] == 0) continue;
        int y = g->adj[x][rndint(g->deg[x])];
        int ok = 1;
        for (int i = 0; i < k; i++) {
            if (X[i] == x || Y[i] == y) { ok = 0; break; }
        }
        if (!ok) continue;
        X[k] = x;
        Y[k] = y;
        k++;
    }
    if (k < dd) return 0;
    for (int i = 0; i < k; i++) edge_del(g, X[i], Y[i]);
    int v = n, w = n + 1;
    g->col[v] = c;
    g->col[w] = 1 - c;
    g->deg[v] = 0;
    g->deg[w] = 0;
    g->n = n + 2;
    for (int i = 0; i < k; i++) {
        edge_add(g, v, X[i]);
        edge_add(g, w, Y[i]);
    }
    return 1;
}

/* Add cross edges between deficient vertices that are not adjacent. Never hurts distances. */
static void fill_graph(Graph *g) {
    int n = g->n;
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] >= dd) continue;
        if (g->col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < dd; j++) {
            int b = R[j];
            if (g->deg[b] >= dd || has_edge(g, a, b)) continue;
            edge_add(g, a, b);
        }
    }
}

static int load_graph(Graph *g) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->col[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(g, u, v)) return 0;
        if (g->deg[u] >= dd || g->deg[v] >= dd) return 0;
        edge_add(g, u, v);
    }
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int x = stk[--sp];
            for (int i = 0; i < g->deg[x]; i++) {
                int y = g->adj[x][i];
                if (g->col[y] == -1) {
                    g->col[y] = 1 - g->col[x];
                    stk[sp++] = y;
                } else if (g->col[y] == g->col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void print_graph(const Graph *g) {
    int m = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) m++;
    printf("%d %d\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) printf("%d %d\n", v, g->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    T0 = clock();
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();

    if (dd < 1 || dd >= MAXDEG || DD < 1 || !load_graph(&G)) {
        printf("2 1\n0 1\n");
        return 0;
    }

    double limit = tl * 0.9;
    fill_graph(&G);
    long long cur = bad_pairs(&G);
    if (cur == 0) {
        BEST = G;
        have_best = 1;
    }
    long long minc = cur, stall = 0;
    const long long STALL = 6000;
    const double TEMP = 0.5;

    while (elapsed() < limit) {
        if (cur == 0) {
            if (!have_best || G.n > BEST.n) {
                BEST = G;
                have_best = 1;
            }
            if (!grow_move(&G)) {
                for (int s = 0; s < 50; s++) switch_move(&G);
            }
            cur = bad_pairs(&G);
            minc = cur;
            stall = 0;
            continue;
        }
        if (!switch_move(&G)) continue;
        long long nc = bad_pairs(&G);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / TEMP)) {
            cur = nc;
        } else {
            switch_undo(&G);
        }
        if (cur < minc) {
            minc = cur;
            stall = 0;
        } else if (++stall > STALL) {
            stall = 0;
            if (have_best) {
                G = BEST;
                cur = 0;
            }
            minc = cur;
        }
    }

    if (have_best) print_graph(&BEST);
    else printf("2 1\n0 1\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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


def _gq_base(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(min(d - 1, 16), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_base(d):
    """PG(2, q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # valid fallback for every d >= 1, D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    base = None
    if D >= 4:
        base = _gq_base(d)
    if base is None and D >= 3:
        base = _pg_base(d)
    if base is not None:
        consider(*base)

    if d >= 2 and D >= 2 and time_limit >= 4:
        start = base if base is not None else best
        budget = max(1.0, 0.80 * time_limit - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=start, timeout=0.92 * time_limit)
            consider(*lib.parse_graph_text(out))
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], list(best[1])
