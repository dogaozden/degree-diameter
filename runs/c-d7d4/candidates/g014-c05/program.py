import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define DMAX 48
#define WMAX (MAXN / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][DMAX];
    int col[MAXN];
} G;

static int dd, DD;
static uint64_t rs = 88172645463325252ULL;
static double deadline_s;
static uint64_t BA[MAXN * WMAX], BB[MAXN * WMAX];
static G cur_g, work_g, best_g;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const G *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++)
        if (g->adj[a][k] == b) return 1;
    return 0;
}

static void add_arc(G *g, int a, int b) { g->adj[a][g->deg[a]++] = b; }

static void add_edge(G *g, int a, int b) {
    add_arc(g, a, b);
    add_arc(g, b, a);
}

static void del_arc(G *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++) {
        if (g->adj[a][k] == b) {
            g->adj[a][k] = g->adj[a][--g->deg[a]];
            return;
        }
    }
}

static void del_edge(G *g, int a, int b) {
    del_arc(g, a, b);
    del_arc(g, b, a);
}

/* Bitset balls of radius r; returns pointer to whichever buffer holds the result. */
static uint64_t *balls(const G *g, int r) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *cu = BA, *nx = BB;
    memset(cu, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cu[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *c = cu + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < g->deg[v]; k++) {
                const uint64_t *c2 = cu + (size_t)g->adj[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *t = cu; cu = nx; nx = t;
    }
    return cu;
}

/* Number of unordered vertex pairs at distance > DD (unreachable included). */
static long cost(const G *g) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *b = balls(g, DD);
    long tot = 0;
    size_t words = (size_t)n * (size_t)W;
    for (size_t i = 0; i < words; i++) tot += popc(b[i]);
    return ((long)n * n - tot) / 2;
}

static int bip(G *g) {
    static int st[MAXN];
    int n = g->n;
    for (int s = 0; s < n; s++) g->col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (g->col[s] >= 0) continue;
        int sp = 0;
        g->col[s] = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int k = 0; k < g->deg[u]; k++) {
                int v = g->adj[u][k];
                if (g->col[v] < 0) {
                    g->col[v] = 1 - g->col[u];
                    st[sp++] = v;
                } else if (g->col[v] == g->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void kdd(G *g) {
    g->n = 2 * dd;
    for (int i = 0; i < g->n; i++) {
        g->deg[i] = 0;
        g->col[i] = (i < dd) ? 0 : 1;
    }
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++)
            add_edge(g, i, dd + j);
}

static int input_graph(G *g) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n >= MAXN - 64 || m < 0) return 0;
    g->n = n;
    for (int i = 0; i < n; i++) { g->deg[i] = 0; g->col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(g, u, v)) return 0;
        if (g->deg[u] >= dd || g->deg[v] >= dd) return 0;
        add_edge(g, u, v);
    }
    return bip(g);
}

/* Join deficient opposite-side vertices (never increases cost). */
static void fill(G *g) {
    static int L[MAXN], R[MAXN];
    int n = g->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] < dd) {
            if (g->col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < dd; j++) {
            int b = R[j];
            if (g->deg[b] < dd && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* Degree-preserving bipartite switches minimising the bad-pair count. Returns final cost. */
static long anneal(G *g, long iters, double T) {
    static int L0[MAXN];
    int n = g->n, nl = 0;
    long c = cost(g);
    for (int v = 0; v < n; v++)
        if (g->col[v] == 0 && g->deg[v] > 0) L0[nl++] = v;
    if (nl < 2) return c;
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline_s) break;
        int a = L0[rndi(nl)];
        int cc = L0[rndi(nl)];
        if (a == cc) continue;
        int b = g->adj[a][rndi(g->deg[a])];
        int e = g->adj[cc][rndi(g->deg[cc])];
        if (has_edge(g, a, e) || has_edge(g, cc, b)) continue;
        del_edge(g, a, b);
        del_edge(g, cc, e);
        add_edge(g, a, e);
        add_edge(g, cc, b);
        long nw = cost(g);
        if (nw <= c || rnd01() < exp(-(double)(nw - c) / T)) {
            c = nw;
        } else {
            del_edge(g, a, e);
            del_edge(g, cc, b);
            add_edge(g, a, b);
            add_edge(g, cc, e);
        }
    }
    return c;
}

/* Add a vertex on the opposite side of `side`, joined to a greedy ball cover of `side`. */
static void add_vertex(G *g, int side) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *b = balls(g, DD - 1);
    uint64_t covered[WMAX];
    static int inS[MAXN];
    int chosen[DMAX];
    int nc = 0;
    memset(covered, 0, sizeof covered);
    memset(inS, 0, sizeof(int) * (size_t)n);
    for (int step = 0; step < dd; step++) {
        int best = -1;
        double bestsc = -1.0;
        for (int s = 0; s < n; s++) {
            if (g->col[s] != side || inS[s]) continue;
            const uint64_t *row = b + (size_t)s * W;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += popc(row[w] & ~covered[w]);
            double sc = gain + 0.9 * rnd01();
            if (sc > bestsc) { bestsc = sc; best = s; }
        }
        if (best < 0) break;
        inS[best] = 1;
        chosen[nc++] = best;
        const uint64_t *brow = b + (size_t)best * W;
        for (int w = 0; w < W; w++) covered[w] |= brow[w];
    }
    int v = n;
    g->col[v] = 1 - side;
    g->deg[v] = 0;
    g->n = n + 1;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g->deg[s] >= dd) {
            int t = g->adj[s][rndi(g->deg[s])];
            del_edge(g, s, t);
        }
        add_edge(g, s, v);
    }
}

/* Random degree-preserving switches accepted only while the graph stays valid. */
static void plateau(G *g, int steps) {
    static int L0[MAXN];
    int n = g->n, nl = 0;
    for (int v = 0; v < n; v++)
        if (g->col[v] == 0 && g->deg[v] > 0) L0[nl++] = v;
    if (nl < 2) return;
    for (int s = 0; s < steps; s++) {
        int a = L0[rndi(nl)];
        int cc = L0[rndi(nl)];
        if (a == cc) continue;
        int b = g->adj[a][rndi(g->deg[a])];
        int e = g->adj[cc][rndi(g->deg[cc])];
        if (has_edge(g, a, e) || has_edge(g, cc, b)) continue;
        del_edge(g, a, b);
        del_edge(g, cc, e);
        add_edge(g, a, e);
        add_edge(g, cc, b);
        if (cost(g) != 0) {
            del_edge(g, a, e);
            del_edge(g, cc, b);
            add_edge(g, a, b);
            add_edge(g, cc, e);
        }
    }
}

static void output(const G *g) {
    long m = 0;
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) m++;
    printf("%d %ld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    deadline_s = budget;

    if (dd < 1 || dd > DMAX - 1 || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    if (!input_graph(&cur_g)) kdd(&cur_g);
    if (cost(&cur_g) != 0) {
        anneal(&cur_g, 20000, 0.4);
        if (cost(&cur_g) != 0) kdd(&cur_g);
    }
    best_g = cur_g;

    const long ITER = 3000;
    long fails = 0;
    while (now_s() < deadline_s - 0.2) {
        if (cur_g.n + 1 >= MAXN) break;
        work_g = cur_g;
        add_vertex(&work_g, rndi(2));
        fill(&work_g);
        long c = anneal(&work_g, ITER, 0.4);
        if (c == 0) {
            cur_g = work_g;
            if (cur_g.n > best_g.n) best_g = cur_g;
            fails = 0;
        } else {
            fails++;
            if (fails % 20 == 0) plateau(&cur_g, 400);
        }
    }
    output(&best_g);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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

    # Phase 1 (short): structured base (GQ for D >= 4, PG for D = 3), growth, twin trials.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng, attempts=30)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.2 * time_limit
        for _ in range(10):
            if time.monotonic() >= trial_end:
                break
            n, e = _duplicate_twins(best_n, best_e, d, rng)
            e = _saturate_edges(n, e, d, rng)
            n, e = _grow(n, e, d, D, trial_end, rng, attempts=30)
            consider(n, e)

    # Phase 2: C annealing search that adds vertices to the best valid graph.
    elapsed = time.monotonic() - start
    budget = 0.85 * time_limit - elapsed - 2.0
    if D >= 2 and budget > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=budget + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
