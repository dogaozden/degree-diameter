import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 40
#define MAXW 32

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static Graph cur, best, work;
static int d_, D_;
static double tend;
static uint64_t rs = 1;
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int has_edge(const Graph *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++)
        if (g->adj[a][k] == b) return 1;
    return 0;
}

static void del_arc(Graph *g, int a, int b) {
    for (int k = 0; k < g->deg[a]; k++) {
        if (g->adj[a][k] == b) {
            g->deg[a]--;
            g->adj[a][k] = g->adj[a][g->deg[a]];
            return;
        }
    }
}

static void add_edge(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void del_edge(Graph *g, int a, int b) {
    del_arc(g, a, b);
    del_arc(g, b, a);
}

/* Number of unordered pairs at distance > D_ (unreachable counts as bad). */
static long cost(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t (*c)[MAXW] = bufA, (*x)[MAXW] = bufB, (*t)[MAXW];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) c[v][w] = 0;
        c[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) x[v][w] = c[v][w];
            for (int k = 0; k < g->deg[v]; k++) {
                int u = g->adj[v][k];
                for (int w = 0; w < W; w++) x[v][w] |= c[u][w];
            }
        }
        t = c;
        c = x;
        x = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int s = 0;
        for (int w = 0; w < W; w++) s += __builtin_popcountll(c[v][w]);
        bad += n - s;
    }
    return bad / 2;
}

/* Two-colour the graph into g->col; returns 0 if not bipartite. */
static int colour(Graph *g) {
    static int q[MAXN];
    for (int v = 0; v < g->n; v++) g->col[v] = -1;
    for (int s = 0; s < g->n; s++) {
        if (g->col[s] >= 0) continue;
        g->col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < g->deg[u]; k++) {
                int w = g->adj[u][k];
                if (g->col[w] < 0) {
                    g->col[w] = 1 - g->col[u];
                    q[t++] = w;
                } else if (g->col[w] == g->col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Degree-preserving bipartite double-edge switches minimising the bad-pair cost. */
static long anneal(Graph *g, long iters, double T0) {
    static int L[MAXN];
    long c = cost(g);
    int nl = 0;
    for (int v = 0; v < g->n; v++)
        if (g->col[v] == 0) L[nl++] = v;
    if (nl < 2) return c;
    double T = T0;
    for (long it = 0; it < iters && c > 0; it++) {
        if ((it & 63) == 0 && now() > tend) break;
        int a = L[rndi(nl)], a2 = L[rndi(nl)];
        if (a == a2 || g->deg[a] == 0 || g->deg[a2] == 0) continue;
        int b = g->adj[a][rndi(g->deg[a])];
        int e = g->adj[a2][rndi(g->deg[a2])];
        if (b == e || has_edge(g, a, e) || has_edge(g, a2, b)) continue;
        del_edge(g, a, b);
        del_edge(g, a2, e);
        add_edge(g, a, e);
        add_edge(g, a2, b);
        long nc = cost(g);
        if (nc <= c || rndf() < exp(-(double)(nc - c) / T)) {
            c = nc;
        } else {
            del_edge(g, a, e);
            del_edge(g, a2, b);
            add_edge(g, a, b);
            add_edge(g, a2, e);
        }
        T *= 0.999;
        if (T < 0.05) T = 0.05;
    }
    return c;
}

/* Insert a new (left, right) pair: take d disjoint edges x-y, replace by a-y and x-b. */
static int add_pair(Graph *g) {
    static int EA[MAXN * MAXD], EB[MAXN * MAXD];
    static char usedL[MAXN], usedR[MAXN];
    static int PX[MAXD], PY[MAXD];
    int d = d_, m = 0;
    if (g->n + 2 > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->col[v] != 0) continue;
        for (int k = 0; k < g->deg[v]; k++) {
            EA[m] = v;
            EB[m] = g->adj[v][k];
            m++;
        }
    }
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int ta = EA[i], tb = EB[i];
        EA[i] = EA[j];
        EB[i] = EB[j];
        EA[j] = ta;
        EB[j] = tb;
    }
    memset(usedL, 0, sizeof usedL);
    memset(usedR, 0, sizeof usedR);
    int np = 0;
    for (int i = 0; i < m && np < d; i++) {
        int x = EA[i], y = EB[i];
        if (usedL[x] || usedR[y]) continue;
        usedL[x] = 1;
        usedR[y] = 1;
        PX[np] = x;
        PY[np] = y;
        np++;
    }
    if (np < d) return 0;
    int a = g->n, b = g->n + 1;
    g->n += 2;
    g->deg[a] = 0;
    g->deg[b] = 0;
    g->col[a] = 0;
    g->col[b] = 1;
    for (int i = 0; i < np; i++) {
        del_edge(g, PX[i], PY[i]);
        add_edge(g, a, PY[i]);
        add_edge(g, PX[i], b);
    }
    return 1;
}

/* Delete vertex v; the last vertex is relabelled into its slot. */
static void remove_vertex(Graph *g, int v) {
    for (int k = 0; k < g->deg[v]; k++) del_arc(g, g->adj[v][k], v);
    g->deg[v] = 0;
    int L = g->n - 1;
    if (v != L) {
        g->deg[v] = g->deg[L];
        g->col[v] = g->col[L];
        for (int k = 0; k < g->deg[L]; k++) g->adj[v][k] = g->adj[L][k];
        for (int k = 0; k < g->deg[v]; k++) {
            int w = g->adj[v][k];
            for (int j = 0; j < g->deg[w]; j++) {
                if (g->adj[w][j] == L) {
                    g->adj[w][j] = v;
                    break;
                }
            }
        }
    }
    g->deg[L] = 0;
    g->n = L;
}

/* Add cross-side edges between deficient vertices (only helps distances). */
static void fill(Graph *g) {
    static int Lf[MAXN], Rf[MAXN];
    int nl = 0, nr = 0, d = d_;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->col[v] == 0) Lf[nl++] = v;
        else Rf[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = Lf[i];
        Lf[i] = Lf[j];
        Lf[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = Rf[i];
        Rf[i] = Rf[j];
        Rf[j] = t;
    }
    for (int i = 0; i < nl; i++)
        for (int j = 0; j < nr; j++) {
            int a = Lf[i], b = Rf[j];
            if (g->deg[a] < d && g->deg[b] < d && !has_edge(g, a, b)) add_edge(g, a, b);
        }
}

static void output(const Graph *g) {
    int m = 0;
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) m++;
    printf("%d %d\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++)
            if (g->adj[v][k] > v) printf("%d %d\n", v, g->adj[v][k]);
}

static void make_kdd(Graph *g, int d) {
    memset(g, 0, sizeof *g);
    g->n = 2 * d;
    for (int i = 0; i < d; i++) {
        g->col[i] = 0;
        g->col[d + i] = 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(g, i, d + j);
}

static int read_graph(Graph *g, int d) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    memset(g, 0, sizeof *g);
    g->n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= d || g->deg[v] >= d || has_edge(g, u, v)) return 0;
        add_edge(g, u, v);
    }
    return colour(g);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 2 || 2 * d_ > MAXN) {
        printf("0 0\n");
        return 0;
    }
    tend = now() + budget;

    if (!read_graph(&cur, d_)) make_kdd(&cur, d_);
    if (cost(&cur) != 0) {
        anneal(&cur, 20000, 0.5);
        if (cost(&cur) != 0) make_kdd(&cur, d_);
    }
    best = cur;

    while (now() < tend) {
        if (rndf() < 0.7) {
            work = cur;
            if (add_pair(&work)) {
                long c = anneal(&work, 4000, 0.5);
                if (c == 0) {
                    cur = work;
                    if (cur.n > best.n) best = cur;
                }
            }
        } else {
            work = cur;
            int k = 1 + rndi(3);
            int ids[8];
            int nk = 0;
            while (nk < k && work.n > 8) {
                int v = rndi(work.n), dup = 0;
                for (int i = 0; i < nk; i++)
                    if (ids[i] == v) dup = 1;
                if (!dup) ids[nk++] = v;
            }
            for (int i = 0; i < nk; i++)
                for (int j = i + 1; j < nk; j++)
                    if (ids[j] > ids[i]) {
                        int t = ids[i];
                        ids[i] = ids[j];
                        ids[j] = t;
                    }
            for (int i = 0; i < nk; i++) remove_vertex(&work, ids[i]);
            fill(&work);
            long c = anneal(&work, 3000, 0.5);
            if (c == 0 && work.n + 4 >= best.n) {
                cur = work;
                if (cur.n > best.n) best = cur;
            }
            if (cur.n + 6 < best.n) cur = best;
        }
    }
    output(&best);
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
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _greedy_cover(cands, ball, full, d, rng, randomize):
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


def _duplicate_twins(n, edges, d, rng):
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


# ----------------------------------------------------------------------------
# Voltage lifts over small (semidirect) groups.
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline):
    """Anneal voltages of a bipartite lift. Returns a valid (n, edges) or None."""
    darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    temp = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return n, e


def _lift_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G_min = best_n // (2 * s) + 1
        G = G_min + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _lift_search(d, D, s, G, mul, rng, slice_end)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# C search driver.
# ----------------------------------------------------------------------------

def _c_search(d, D, n, edges, seed, budget):
    """Run the C annealer/grower from a valid graph. Returns (n, edges) or None."""
    if d > 39 or n > 2000 or budget < 1.0:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 5.0)
        return lib.parse_graph_text(out)
    except (RuntimeError, ValueError, OSError):
        return None


# ----------------------------------------------------------------------------
# Driver. Budget T = 0.85 * time_limit:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   L  voltage lifts over small groups
#   C  C engine: pair growth + annealing + kill/repair from the best graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase A: structured base, grown, then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, at(0.03), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.06)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.25):
        _lift_phase(d, D, lambda: best_n, at(0.25), rng, consider)

    # Phase C: C engine from the best valid graph found so far.
    if D >= 2:
        budget = at(1.0) - time.monotonic() - 1.0
        res = _c_search(d, D, best_n, best_e, seed, budget)
        if res is not None:
            consider(*res)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
