import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: kill-repair annealing with bitset ball costs.
#
# State: a valid-or-nearly-valid bipartite graph of order n.
# Cost = number of unordered vertex pairs at distance > D (bitset balls).
# Moves: bipartite double-edge switches (degrees kept) and edge additions
# between deficient opposite-side vertices. Annealing drives the cost to 0.
# Growth: when cost is 0, add a vertex on one side whose neighbourhood is a
# greedy cover of all vertices within distance D-1 (each neighbour's ball).
# Stagnation: restore the best valid graph and delete a few random vertices
# (kill), then repair by annealing and regrow.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1024
#define MAXDEG 32
#define MAXW 16
#define MAXK 8

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
    int col[MAXN];
} G;

static G cur, best;
static int bestn = -1;
static int dd, DD;
static double tlim;
static int W;
static uint64_t rs;
static uint64_t ball[MAXK + 1][MAXN][MAXW];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void compute_balls(const G *g) {
    int n = g->n;
    W = (n + 63) / 64;
    if (W < 1) W = 1;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) ball[0][v][w] = 0;
        ball[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 1; k <= DD; k++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) ball[k][v][w] = ball[k - 1][v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                for (int w = 0; w < W; w++) ball[k][v][w] |= ball[k - 1][u][w];
            }
        }
    }
}

static long cost_of(const G *g) {
    compute_balls(g);
    long bad = 0;
    int n = g->n;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(ball[DD][v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(const G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) return 1;
    return 0;
}

static void rem_dir(G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->adj[a][i] == b) {
            g->adj[a][i] = g->adj[a][--g->deg[a]];
            return;
        }
    }
}

static void add_edge(G *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void rem_edge(G *g, int a, int b) {
    rem_dir(g, a, b);
    rem_dir(g, b, a);
}

static int read_graph(G *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 0 || n > MAXN - 2 || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->col[v] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(g, u, v)) return 0;
        if (g->deg[u] >= dd || g->deg[v] >= dd) return 0;
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->col[s] >= 0) continue;
        g->col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int i = 0; i < g->deg[x]; i++) {
                int y = g->adj[x][i];
                if (g->col[y] < 0) {
                    g->col[y] = 1 - g->col[x];
                    queue[qt++] = y;
                } else if (g->col[y] == g->col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add a vertex of colour s joined to a greedy cover of the old vertices. */
static int try_grow(G *g, int s, int partial) {
    int n = g->n;
    if (n >= MAXN - 1 || n == 0) return 0;
    int K = DD - 1;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int covered = 0, nch = 0;
    int chosen[MAXDEG];
    while (covered < n && nch < dd) {
        int bestg = 0, pick = -1, cnt = 0;
        for (int u = 0; u < n; u++) {
            if (g->col[u] == s || g->deg[u] >= dd) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += popc(ball[K][u][w] & ~cov[w]);
            if (gain <= 0) continue;
            if (gain > bestg) { bestg = gain; pick = u; cnt = 1; }
            else if (gain == bestg) { cnt++; if (irand(cnt) == 0) pick = u; }
        }
        if (pick < 0) break;
        chosen[nch++] = pick;
        for (int w = 0; w < W; w++) cov[w] |= ball[K][pick][w];
        covered += bestg;
    }
    if (nch == 0) return 0;
    if (!partial && covered < n) return 0;
    int v = n;
    g->n = n + 1;
    g->col[v] = s;
    g->deg[v] = 0;
    for (int i = 0; i < nch; i++) add_edge(g, v, chosen[i]);
    return 1;
}

static int try_addedge(G *g, int *A, int *B) {
    int n = g->n;
    for (int tries = 0; tries < 30; tries++) {
        int a = irand(n), b = irand(n);
        if (g->col[a] == g->col[b]) continue;
        if (g->deg[a] >= dd || g->deg[b] >= dd) continue;
        if (has_edge(g, a, b)) continue;
        add_edge(g, a, b);
        *A = a; *B = b;
        return 1;
    }
    return 0;
}

/* Bipartite double-edge switch: a-b, c-e  ->  a-e, c-b (a, c same colour). */
static int try_switch(G *g, int *A, int *B, int *C, int *E) {
    int n = g->n;
    for (int tries = 0; tries < 20; tries++) {
        int a = irand(n);
        if (g->deg[a] == 0) continue;
        int c = irand(n);
        if (c == a || g->col[c] != g->col[a] || g->deg[c] == 0) continue;
        int b = g->adj[a][irand(g->deg[a])];
        int e = g->adj[c][irand(g->deg[c])];
        if (e == b) continue;
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        rem_edge(g, a, b);
        rem_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        *A = a; *B = b; *C = c; *E = e;
        return 1;
    }
    return 0;
}

static void undo_switch(G *g, int a, int b, int c, int e) {
    rem_edge(g, a, e);
    rem_edge(g, c, b);
    add_edge(g, a, b);
    add_edge(g, c, e);
}

/* Delete vertex v; the last vertex is moved into slot v. */
static void remove_vertex(G *g, int v) {
    for (int i = 0; i < g->deg[v]; i++) rem_dir(g, g->adj[v][i], v);
    g->deg[v] = 0;
    int last = g->n - 1;
    if (v != last) {
        g->deg[v] = g->deg[last];
        g->col[v] = g->col[last];
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[last][i];
            g->adj[v][i] = u;
            for (int j = 0; j < g->deg[u]; j++) {
                if (g->adj[u][j] == last) { g->adj[u][j] = v; break; }
            }
        }
    }
    g->n = last;
}

static void kick(void) {
    if (bestn > 0) cur = best;
    int k = 1 + irand(3);
    for (int i = 0; i < k && cur.n > 2; i++) remove_vertex(&cur, irand(cur.n));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlim = atof(argv[4]);
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (dd < 1 || dd > MAXDEG - 1 || DD < 1 || DD > MAXK) { printf("0 0\n"); return 0; }
    if (!read_graph(&cur)) { printf("0 0\n"); return 0; }

    long c = cost_of(&cur);
    long bestc = c;
    if (c == 0) { best = cur; bestn = cur.n; }
    const double T = 0.35;
    long stagn = 0;
    const long limit = 3000;

    while (now() < tlim) {
        if (c == 0) {
            if (cur.n > bestn) { best = cur; bestn = cur.n; }
            compute_balls(&cur);
            int s = irand(2);
            int ok = try_grow(&cur, s, 0);
            if (!ok) ok = try_grow(&cur, 1 - s, 0);
            if (!ok) ok = try_grow(&cur, s, 1);
            if (!ok) kick();
            c = cost_of(&cur);
            bestc = c;
            stagn = 0;
            continue;
        }

        int A = 0, B = 0, C2 = 0, E = 0, kind = 0, applied = 0;
        if (irand(8) == 0) {
            kind = 1;
            applied = try_addedge(&cur, &A, &B);
        } else {
            kind = 2;
            applied = try_switch(&cur, &A, &B, &C2, &E);
        }
        if (applied) {
            long nc = cost_of(&cur);
            if (nc <= c || urand() < exp(-(double)(nc - c) / T)) {
                c = nc;
            } else {
                if (kind == 1) rem_edge(&cur, A, B);
                else undo_switch(&cur, A, B, C2, E);
            }
        }
        if (c < bestc) {
            bestc = c;
            stagn = 0;
        } else if (++stagn > limit) {
            kick();
            c = cost_of(&cur);
            bestc = c;
            stagn = 0;
        }
    }

    if (bestn <= 0) { printf("0 0\n"); return 0; }
    int m = 0;
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++)
            if (v < best.adj[v][i]) m++;
    printf("%d %d\n", best.n, m);
    for (int v = 0; v < best.n; v++)
        for (int i = 0; i < best.deg[v]; i++)
            if (v < best.adj[v][i]) printf("%d %d\n", v, best.adj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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


def _largest_pp(limit, cap):
    """Largest prime power q <= min(limit, cap), or None."""
    for q in range(min(limit, cap), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base = None
    if D >= 4:
        q = _largest_pp(d - 1, 16)
        if q is not None:
            base = _gq_w(q)
    elif D == 3:
        q = _largest_pp(d - 1, 13)
        if q is not None:
            base = lib.projective_plane_incidence(q)
    if base is not None:
        consider(*base)

    # Skip the search when the base already meets the Moore bound.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Kill-repair annealing in C, starting from the best valid graph so far.
    budget = 0.72 * time_limit - (time.monotonic() - t0)
    if D >= 2 and budget > 2 and d <= 31:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=(best_n, best_e), timeout=budget + 10)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
