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

#define MAXN 1600
#define MAXD 24
#define MAXW ((MAXN + 63) / 64)
#define ANN_ITERS 600

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} Graph;

static Graph cur, snap, bestG, tmpG;
static long bestn = -1;
static int d_, D_;
static uint64_t rs = 88172645463325252ULL;
static double budget_s = 1.0;
static clock_t t0;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t ballout[MAXN * MAXW];
static uint64_t ballcov[MAXN * MAXW];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* out[v] = bitmask of vertices within distance r of v. */
static void compute_balls(const Graph *g, int r, uint64_t *out) {
    int n = g->n, w = (n + 63) / 64;
    uint64_t *cb = bufA, *nb = bufB;
    memset(cb, 0, sizeof(uint64_t) * (size_t)n * w);
    for (int v = 0; v < n; v++) cb[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nb + (size_t)v * w;
            const uint64_t *src = cb + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * w);
            for (int k = 0; k < g->deg[v]; k++) {
                const uint64_t *q = cb + (size_t)g->adj[v][k] * w;
                for (int j = 0; j < w; j++) dst[j] |= q[j];
            }
        }
        uint64_t *t = cb;
        cb = nb;
        nb = t;
    }
    memcpy(out, cb, sizeof(uint64_t) * (size_t)n * w);
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long cost_of(const Graph *g) {
    int n = g->n, w = (n + 63) / 64;
    compute_balls(g, D_, ballout);
    long s = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *b = ballout + (size_t)v * w;
        for (int j = 0; j < w; j++) c += popc(b[j]);
        s += n - c;
    }
    return s / 2;
}

static int has_edge(const Graph *g, int u, int v) {
    for (int k = 0; k < g->deg[u]; k++)
        if (g->adj[u][k] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_arc(Graph *g, int u, int v) {
    int dg = g->deg[u];
    for (int k = 0; k < dg; k++) {
        if (g->adj[u][k] == v) {
            g->adj[u][k] = g->adj[u][dg - 1];
            g->deg[u] = dg - 1;
            return;
        }
    }
}

static void del_edge(Graph *g, int u, int v) {
    del_arc(g, u, v);
    del_arc(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    int n = src->n;
    dst->n = n;
    for (int v = 0; v < n; v++) {
        dst->deg[v] = src->deg[v];
        dst->col[v] = src->col[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Cross-side greedy edges between deficient vertices (only shortens distances). */
static void fill_graph(Graph *g) {
    static int L[MAXN], R[MAXN];
    int n = g->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] < d_) {
            if (g->col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && g->deg[a] < d_; j++) {
            int b = R[j];
            if (g->deg[b] < d_ && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* Append a vertex on the side opposite `side`, joined to a greedy cover of `side`. */
static void add_vertex(Graph *g, int side) {
    int n = g->n, w = (n + 63) / 64;
    compute_balls(g, D_ - 1, ballcov);
    uint64_t covered[MAXW];
    memset(covered, 0, sizeof(covered));
    static int used[MAXN];
    memset(used, 0, sizeof(int) * n);
    int chosen[MAXD], nc = 0;
    for (int it = 0; it < d_; it++) {
        int best = -1;
        double bsc = -1.0;
        for (int s = 0; s < n; s++) {
            if (g->col[s] != side || used[s]) continue;
            int gain = 0;
            const uint64_t *b = ballcov + (size_t)s * w;
            for (int j = 0; j < w; j++) gain += popc(b[j] & ~covered[j]);
            double sc = gain + 0.5 * rnd01();
            if (sc > bsc) {
                bsc = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const uint64_t *b = ballcov + (size_t)best * w;
        for (int j = 0; j < w; j++) covered[j] |= b[j];
    }
    int v = n;
    g->n = n + 1;
    g->deg[v] = 0;
    g->col[v] = 1 - side;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g->deg[s] >= d_) {
            int t = g->adj[s][rndint(g->deg[s])];
            del_edge(g, s, t);
        }
        add_edge(g, s, v);
    }
}

/* Bipartite double-edge switches (degrees kept) minimising bad pairs. True if cost reaches 0. */
static int anneal(Graph *g, int iters) {
    static int S0[MAXN];
    int ns = 0;
    for (int v = 0; v < g->n; v++)
        if (g->col[v] == 0) S0[ns++] = v;
    if (ns == 0) return cost_of(g) == 0;
    long cc = cost_of(g);
    for (int it = 0; it < iters && cc > 0; it++) {
        if (elapsed() > budget_s) break;
        int a = S0[rndint(ns)];
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndint(g->deg[a])];
        int c = S0[rndint(ns)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->adj[c][rndint(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nw = cost_of(g);
        if (nw <= cc || (nw == cc + 1 && rnd01() < 0.1)) {
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

/* Remove k vertices forming a connected-ish cluster, then compact ids. */
static void kill_random(Graph *g, int k) {
    int n = g->n;
    static char dead[MAXN];
    static int front[MAXN];
    memset(dead, 0, sizeof(char) * n);
    int v0 = rndint(n);
    dead[v0] = 1;
    int cnt = 1, nf = 0;
    front[nf++] = v0;
    while (cnt < k && nf > 0) {
        int idx = rndint(nf);
        int x = front[idx];
        front[idx] = front[--nf];
        int dg = g->deg[x];
        if (dg == 0) continue;
        int off = rndint(dg);
        for (int t = 0; t < dg && cnt < k; t++) {
            int u = g->adj[x][(off + t) % dg];
            if (!dead[u]) {
                dead[u] = 1;
                cnt++;
                front[nf++] = u;
            }
        }
    }
    while (cnt < k) {
        int u = rndint(n);
        if (!dead[u]) {
            dead[u] = 1;
            cnt++;
        }
    }
    static int map[MAXN];
    int m = 0;
    for (int v = 0; v < n; v++) map[v] = dead[v] ? -1 : m++;
    tmpG.n = m;
    for (int v = 0; v < n; v++) {
        if (dead[v]) continue;
        int nv = map[v];
        tmpG.col[nv] = g->col[v];
        tmpG.deg[nv] = 0;
        for (int q = 0; q < g->deg[v]; q++) {
            int u = g->adj[v][q];
            if (!dead[u]) tmpG.adj[nv][tmpG.deg[nv]++] = map[u];
        }
    }
    copy_graph(g, &tmpG);
}

/* Delete random edges while the diameter bound still holds. */
static void prune_redundant(Graph *g, int maxtests) {
    static int eu[MAXN * MAXD], ev[MAXN * MAXD], ord[MAXN * MAXD];
    int m = 0;
    for (int u = 0; u < g->n; u++) {
        for (int k = 0; k < g->deg[u]; k++) {
            int v = g->adj[u][k];
            if (u < v) {
                eu[m] = u;
                ev[m] = v;
                m++;
            }
        }
    }
    for (int i = 0; i < m; i++) ord[i] = i;
    shuffle_int(ord, m);
    int tests = 0;
    for (int i = 0; i < m && tests < maxtests; i++) {
        if (elapsed() > budget_s) break;
        int u = eu[ord[i]], v = ev[ord[i]];
        if (!has_edge(g, u, v)) continue;
        tests++;
        del_edge(g, u, v);
        if (cost_of(g) != 0) add_edge(g, u, v);
    }
}

static void record_best(void) {
    if ((long)cur.n > bestn) {
        bestn = cur.n;
        copy_graph(&bestG, &cur);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    budget_s = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        printf("0 0\n");
        return 0;
    }
    t0 = clock();
    if (n0 == 0 && m0 == 0) {
        cur.n = 2 * d_;
        for (int i = 0; i < d_; i++) {
            cur.col[i] = 0;
            cur.col[d_ + i] = 1;
        }
        for (int i = 0; i < d_; i++)
            for (int j = 0; j < d_; j++) add_edge(&cur, i, d_ + j);
    } else {
        if (n0 < 1 || n0 > MAXN - 2 || m0 < 0) {
            printf("0 0\n");
            return 0;
        }
        cur.n = n0;
        for (int v = 0; v < n0; v++) cur.deg[v] = 0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                printf("0 0\n");
                return 0;
            }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
                printf("0 0\n");
                return 0;
            }
            if (cur.deg[u] >= d_ || cur.deg[v] >= d_ || has_edge(&cur, u, v)) {
                printf("0 0\n");
                return 0;
            }
            add_edge(&cur, u, v);
        }
        for (int v = 0; v < n0; v++) cur.col[v] = -1;
        static int stk[MAXN];
        for (int s = 0; s < n0; s++) {
            if (cur.col[s] != -1) continue;
            cur.col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0) {
                int x = stk[--sp];
                for (int k = 0; k < cur.deg[x]; k++) {
                    int y = cur.adj[x][k];
                    if (cur.col[y] == -1) {
                        cur.col[y] = 1 - cur.col[x];
                        stk[sp++] = y;
                    } else if (cur.col[y] == cur.col[x]) {
                        printf("0 0\n");
                        return 0;
                    }
                }
            }
        }
    }

    if (cost_of(&cur) != 0) {
        fill_graph(&cur);
        if (!anneal(&cur, 200000)) {
            printf("0 0\n");
            return 0;
        }
    }
    record_best();

    while (elapsed() < budget_s) {
        copy_graph(&snap, &cur);
        if (cur.n > 8 && rnd01() < 0.35) kill_random(&cur, 1 + rndint(3));
        if (cur.n + 1 < MAXN) add_vertex(&cur, rndint(2));
        fill_graph(&cur);
        if (anneal(&cur, ANN_ITERS)) {
            fill_graph(&cur);
            if (cur.n < snap.n - 1) {
                copy_graph(&cur, &snap);
                continue;
            }
            record_best();
            if (rnd01() < 0.25) prune_redundant(&cur, 120);
            if ((long)cur.n < bestn - 3) copy_graph(&cur, &bestG);
        } else {
            copy_graph(&cur, &snap);
        }
    }

    if (bestn < 0) {
        printf("0 0\n");
        return 0;
    }
    long m = 0;
    for (int u = 0; u < bestG.n; u++)
        for (int k = 0; k < bestG.deg[u]; k++)
            if (bestG.adj[u][k] > u) m++;
    printf("%d %ld\n", bestG.n, m);
    for (int u = 0; u < bestG.n; u++)
        for (int k = 0; k < bestG.deg[u]; k++) {
            int v = bestG.adj[u][k];
            if (v > u) printf("%d %d\n", u, v);
        }
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
    """Incidence graph of points and lines of the generalized quadrangle W(q) (diameter 4)."""
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
    """W(q) incidence graph for the largest prime power q <= min(d - 1, 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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


def _spare_matching_base(n0, e0, d, rng, keep_free):
    """On a point-line base (points first), add cross edges to use spare slots, keeping some free."""
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


def build(d, D, seed, time_limit):
    t_start = time.monotonic()

    def at(frac):
        return t_start + frac * time_limit

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base_n, base_e = best_n, list(best_e)
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        base_is_gq = base is not None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2 and best_n < bound:
        trial_end = at(0.16)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Spare-slot matching on the quadrangle base.
    if base_is_gq and best_n < bound:
        spare_end = at(0.22)
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    # C engine: kill / repair / regrow search from the best valid graph.
    if D >= 2 and best_n < bound:
        budget = at(0.90) - time.monotonic() - 3.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
