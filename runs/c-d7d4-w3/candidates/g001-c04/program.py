import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 32
#define ITERS 2000
#define TEMP 0.5

static int d, D, n;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];
static uint64_t BA[MAXN][MAXW], BB[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static double budget = 1.0;
static clock_t t0;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} Snap;
static Snap good;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int timeout_hit(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC >= budget;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* BA := ball of radius r around every vertex (bitsets over the first n vertices). */
static void compute_balls(int r) {
    int wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        memset(BA[v], 0, (size_t)wn * sizeof(uint64_t));
        BA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < wn; w++) BB[v][w] = BA[v][w];
            for (int t = 0; t < deg[v]; t++) {
                int u = adj[v][t];
                for (int w = 0; w < wn; w++) BB[v][w] |= BA[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < wn; w++) BA[v][w] = BB[v][w];
    }
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long cost_bad(void) {
    int wn = (n + 63) >> 6;
    compute_balls(D);
    long c = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < wn; w++) cnt += pc64(BA[v][w]);
        c += n - cnt;
    }
    return c / 2;
}

/* Add a vertex on a random side, joined greedily to a cover of the opposite side. */
static void add_vertex(void) {
    int s = rndi(2);
    int wn = (n + 63) >> 6;
    compute_balls(D - 1);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    static int used[MAXN];
    for (int v = 0; v < n; v++) used[v] = 0;
    while (nc < d) {
        long best = -1;
        int bi = -1;
        for (int u = 0; u < n; u++) {
            if (side[u] == s || deg[u] >= d || used[u]) continue;
            long g = 0;
            for (int w = 0; w < wn; w++) g += pc64(BA[u][w] & ~cov[w]);
            if (g == 0) continue;
            long score = g * 4096 + rndi(4096);
            if (score > best) {
                best = score;
                bi = u;
            }
        }
        if (bi < 0) break;
        used[bi] = 1;
        chosen[nc++] = bi;
        for (int w = 0; w < wn; w++) cov[w] |= BA[bi][w];
    }
    int v = n++;
    side[v] = s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) add_edge(v, chosen[i]);
}

/* Join deficient opposite-side vertices. */
static void fill_deficient(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d) continue;
        if (side[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    for (int i = 0; i < nl; i++) {
        for (int j = 0; j < nr; j++) {
            int a = L[i], b = R[j];
            if (deg[a] < d && deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int pick_side0(void) {
    for (int t = 0; t < 10000; t++) {
        int v = rndi(n);
        if (side[v] == 0 && deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double T) {
    long cur = cost_bad();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && timeout_hit()) break;
        int a = pick_side0();
        int c = pick_side0();
        if (a < 0 || c < 0) break;
        int b = adj[a][rndi(deg[a])];
        int e = adj[c][rndi(deg[c])];
        if (a == c || b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_bad();
        long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->side, side, sizeof side);
}

static void load(const Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
    memcpy(side, s->side, sizeof side);
}

static int read_graph(void) {
    int m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN - 1 || m < 0) return 0;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        side[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    q[t++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    t0 = clock();
    if (d < 1 || d > MAXD || D < 2) return 1;
    if (!read_graph()) {
        printf("0 0\n");
        return 0;
    }
    save(&good);
    while (n < MAXN - 1 && !timeout_hit()) {
        add_vertex();
        fill_deficient();
        long c = anneal(ITERS, TEMP);
        if (c == 0) save(&good);
        else load(&good);
    }
    load(&good);
    long m = 0;
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) m++;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (adj[u][k] > u) printf("%d %d\n", u, adj[u][k]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q + 1, diameter 4."""
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
    """Generalized quadrangle W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins (same neighbourhood) in random order while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            consider(*base)

    # Short twin-duplication stage to enlarge the start graph.
    if D >= 2:
        base_n, base_e = best_n, list(best_e)
        for _ in range(4):
            if time.monotonic() > start + 0.1 * time_limit:
                break
            n, e = _duplicate_twins(base_n, base_e, d, rng)
            consider(n, e)

    # Main stage: C annealing engine that repeatedly adds one vertex and repairs by switches.
    if D >= 2 and d <= 30:
        remaining = end - time.monotonic()
        if remaining > 5:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 3.0, 2)],
                                 stdin_graph=(best_n, best_e), timeout=remaining)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
