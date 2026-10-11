import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXD 16
#define ANN_ITERS 300

typedef struct {
    int n;
    int deg[MAXN];
    int nb[MAXN][MAXD];
    int col[MAXN];
} G;

static G cur, best, snap, tmpg;
static int dd, DD, maxn;
static uint64_t rs = 88172645463325252ULL;
static double budget;
static clock_t t0;
static uint64_t B1[MAXN][MAXW], B2[MAXN][MAXW];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) if (g->nb[u][i] == v) return 1;
    return 0;
}
static void del_arc(G *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++) {
        if (g->nb[u][i] == v) { g->nb[u][i] = g->nb[u][--g->deg[u]]; return; }
    }
}
static void del_edge(G *g, int u, int v) { del_arc(g, u, v); del_arc(g, v, u); }
static void add_edge(G *g, int u, int v) {
    g->nb[u][g->deg[u]++] = v;
    g->nb[v][g->deg[v]++] = u;
}

/* bitmask balls of radius r, stored in B1 */
static void compute_balls(const G *g, int r) {
    int n = g->n, W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) B1[v][w] = 0;
        B1[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B2[v][w] = B1[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->nb[v][i];
                for (int w = 0; w < W; w++) B2[v][w] |= B1[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) B1[v][w] = B2[v][w];
    }
}

/* number of unordered pairs at distance > r (unreachable counts) */
static long long bad_pairs(const G *g, int r) {
    int n = g->n, W = (n + 63) / 64;
    compute_balls(g, r);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(B1[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* add random cross-side edges between deficient vertices */
static void fill(G *g) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= dd) continue;
        if (g->col[v] == 0) L[nl++] = v; else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < dd; j++) {
            int b = R[j];
            if (g->deg[b] >= dd || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

/* degree-preserving bipartite double-edge switches minimising bad pairs */
static int anneal(G *g, int iters) {
    static int S0[MAXN];
    int ns0 = 0;
    for (int v = 0; v < g->n; v++) if (g->col[v] == 0) S0[ns0++] = v;
    long long cc = bad_pairs(g, DD);
    if (ns0 < 2) return cc == 0;
    for (int it = 0; it < iters && cc > 0; it++) {
        if ((it & 15) == 0 && elapsed() > budget) break;
        int a = S0[rndi(ns0)];
        if (g->deg[a] == 0) continue;
        int b = g->nb[a][rndi(g->deg[a])];
        int c = S0[rndi(ns0)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->nb[c][rndi(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long long nw = bad_pairs(g, DD);
        if (nw <= cc || (nw == cc + 1 && rndf() < 0.1)) {
            cc = nw;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return cc == 0;
}

/* add a vertex on the opposite side of `side`, joined to a greedy cover of `side` */
static int add_vertex(G *g, int side) {
    int n = g->n, W = (n + 63) / 64;
    static uint64_t cov[MAXW];
    static char used[MAXN];
    static int chosen[MAXD];
    compute_balls(g, DD - 1);
    for (int w = 0; w < W; w++) cov[w] = 0;
    for (int v = 0; v < n; v++) used[v] = 0;
    int nc = 0;
    for (int k = 0; k < dd; k++) {
        int bs = -1;
        double bsc = -1.0;
        for (int s = 0; s < n; s++) {
            if (g->col[s] != side || used[s]) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += pc(B1[s][w] & ~cov[w]);
            double sc = gain + 0.5 * rndf();
            if (sc > bsc) { bsc = sc; bs = s; }
        }
        if (bs < 0) break;
        used[bs] = 1;
        chosen[nc++] = bs;
        for (int w = 0; w < W; w++) cov[w] |= B1[bs][w];
    }
    int v = n;
    g->n = n + 1;
    g->deg[v] = 0;
    g->col[v] = 1 - side;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g->deg[s] >= dd) {
            int t = g->nb[s][rndi(g->deg[s])];
            del_edge(g, s, t);
        }
        add_edge(g, s, v);
    }
    return v;
}

/* remove k random vertices, relabel, keep colours */
static void kill_vertices(G *g, int k) {
    static char dead[MAXN];
    static int remap[MAXN];
    int n = g->n;
    for (int v = 0; v < n; v++) dead[v] = 0;
    int cnt = 0;
    while (cnt < k && cnt < n) {
        int x = rndi(n);
        if (!dead[x]) { dead[x] = 1; cnt++; }
    }
    int m = 0;
    for (int v = 0; v < n; v++) remap[v] = dead[v] ? -1 : m++;
    tmpg.n = m;
    for (int v = 0; v < n; v++) {
        if (dead[v]) continue;
        int nv = remap[v];
        tmpg.deg[nv] = 0;
        tmpg.col[nv] = g->col[v];
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->nb[v][i];
            if (!dead[u]) tmpg.nb[nv][tmpg.deg[nv]++] = remap[u];
        }
    }
    *g = tmpg;
}

static void print_graph(const G *g) {
    int m = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->nb[v][i] > v) m++;
    printf("%d %d\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->nb[v][i] > v) printf("%d %d\n", v, g->nb[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("1 0\n"); return 0; }
    t0 = clock();
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    budget = atof(argv[4]);
    maxn = atoi(argv[5]);
    if (maxn > MAXN - 2) maxn = MAXN - 2;
    if (dd < 1 || dd > MAXD - 1 || DD < 2) { printf("1 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = m0 = 0;
    if (n0 < 1 || n0 > MAXN - 2) { printf("1 0\n"); return 0; }
    cur.n = n0;
    for (int v = 0; v < n0; v++) { cur.deg[v] = 0; cur.col[v] = -1; }
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) continue;
        if (cur.deg[u] >= MAXD || cur.deg[v] >= MAXD) continue;
        add_edge(&cur, u, v);
    }
    /* 2-colour the start graph; a conflict means the input is not bipartite */
    {
        static int stk[MAXN];
        int bad = 0;
        for (int s = 0; s < n0; s++) {
            if (cur.col[s] != -1) continue;
            cur.col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0) {
                int u = stk[--sp];
                for (int i = 0; i < cur.deg[u]; i++) {
                    int w = cur.nb[u][i];
                    if (cur.col[w] == -1) { cur.col[w] = 1 - cur.col[u]; stk[sp++] = w; }
                    else if (cur.col[w] == cur.col[u]) bad = 1;
                }
            }
        }
        if (bad) { printf("1 0\n"); return 0; }
    }
    if (bad_pairs(&cur, DD) != 0) {
        /* start not valid: still print it, the caller validates */
        print_graph(&cur);
        return 0;
    }

    best = cur;
    while (elapsed() < budget) {
        snap = cur;
        if (cur.n + 1 <= maxn && rndf() < 0.6) {
            add_vertex(&cur, rndi(2));
            fill(&cur);
            if (anneal(&cur, ANN_ITERS)) {
                if (cur.n > best.n) best = cur;
            } else {
                cur = snap;
            }
        } else {
            int k = 1 + rndi(3);
            if (cur.n <= k + 2) { cur = snap; continue; }
            kill_vertices(&cur, k);
            fill(&cur);
            if (anneal(&cur, ANN_ITERS)) {
                if (cur.n < best.n - 3) cur = best;
                else if (cur.n > best.n) best = cur;
            } else {
                cur = snap;
            }
        }
    }
    print_graph(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

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
    """Generalized quadrangle incidence graph W(q), largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices (keeps diameter <= D)."""
    if D < 2:
        return n, edges
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random edges whose removal keeps diameter <= D."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


# ----------------------------------------------------------------------------
# Python fallback search (used only if the C engine is unavailable).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Degree-preserving bipartite switches minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _py_lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow search in Python, anchored to the best graph."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 60, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# C engine driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, n, edges, c_budget, timeout):
    """Run the C anneal/kill/add search from (n, edges). Returns a validated (n, edges) or None."""
    try:
        cap = min(lib.moore_bound(d, D), 1090)
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", cap],
                        stdin_graph=(n, edges), timeout=timeout)
        cn, ce = lib.parse_graph_text(out)
        if lib.is_valid(cn, ce, d, D):
            return cn, ce
    except Exception:
        return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.90 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, optimal for D <= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best_e = list(best_e)
    if D <= 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: W(q) quadrangle for D >= 4, projective plane for D = 3.
    base = _best_gq(d) if D >= 4 else None
    if base is None:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
        consider(n1, e1)

    # Prune redundant edges, then regrow (frees degree for new vertices).
    if time.monotonic() < hard_end:
        pe = _prune_redundant(best_n, best_e, D, rng, start + 0.16 * time_limit, 160)
        n2, e2 = _grow(best_n, pe, d, D, start + 0.20 * time_limit, rng)
        consider(n2, e2)

    # Main search in C, given most of the budget.
    c_budget = 0.70 * time_limit - (time.monotonic() - start)
    if c_budget > 2:
        timeout = max(1.0, hard_end - time.monotonic())
        res = _c_search(d, D, seed, best_n, best_e, c_budget, timeout)
        if res is not None:
            consider(*res)

    # Python fallback / leftover time.
    rem = hard_end - time.monotonic()
    if rem > 1:
        _py_lns(best_n, best_e, d, D, hard_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
