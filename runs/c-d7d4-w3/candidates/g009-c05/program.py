# New in this version: a native C stage. The C engine keeps a bipartite graph with
# max degree d and runs kill-repair-regrow LNS. Killed vertices are repaired by a new
# vertex whose neighbourhood greedily covers all pairs within distance D-1, and the
# result is cleaned up by simulated annealing over degree-preserving double-edge
# switches. Cost is the exact number of vertex pairs at distance > D, computed with
# bitset balls. The Python side keeps the GQ/PG + twin/grow pipeline as the start and
# validates every returned graph with lib.is_valid.
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

#define MAXN 3000
#define DMAX 24
#define MAXW ((MAXN + 63) / 64)

typedef uint64_t Row[MAXW];

typedef struct {
    int n;
    unsigned char col[MAXN];
    int deg[MAXN];
    int nb[MAXN][DMAX];
} G;

static int d_, D_;
static uint64_t rs = 1;
static G cur, best, work, tmpg;
static Row BA[MAXN], BB[MAXN], BT[MAXN];
static int Lbuf[MAXN], Rbuf[MAXN], mapv[MAXN], L0[MAXN], colr[MAXN];
static char killed[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int timeup(double tend) { return (double)clock() >= tend; }

static int has_edge(const G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->nb[a][i] == b) return 1;
    return 0;
}

static void add_edge(G *g, int a, int b) {
    g->nb[a][g->deg[a]++] = b;
    g->nb[b][g->deg[b]++] = a;
}

static void del_arc(G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->nb[a][i] == b) {
            g->nb[a][i] = g->nb[a][g->deg[a] - 1];
            g->deg[a]--;
            return;
        }
    }
}

static void del_edge(G *g, int a, int b) {
    del_arc(g, a, b);
    del_arc(g, b, a);
}

static void copyg(G *dst, const G *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->col[v] = src->col[v];
        dst->deg[v] = src->deg[v];
        memcpy(dst->nb[v], src->nb[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* out[v] = bitset of vertices within distance `rounds` of v. */
static void balls(int n, const G *g, int rounds, Row *out) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < rounds; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) BT[v][w] = out[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->nb[v][i];
                for (int w = 0; w < W; w++) BT[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) out[v][w] = BT[v][w];
    }
}

/* Number of unordered vertex pairs at distance > D_. */
static long long cost_of(const G *g) {
    int n = g->n, W = (n + 63) / 64;
    balls(n, g, D_, BA);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BA[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add every possible cross-side edge between deficient vertices (never hurts the cost). */
static void fill(G *g) {
    int n = g->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] >= d_) continue;
        if (g->col[v] == 0) Lbuf[nl++] = v;
        else Rbuf[nr++] = v;
    }
    shuffle(Lbuf, nl);
    shuffle(Rbuf, nr);
    for (int i = 0; i < nl; i++) {
        int a = Lbuf[i];
        for (int j = 0; j < nr && g->deg[a] < d_; j++) {
            int b = Rbuf[j];
            if (g->deg[b] < d_ && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* New vertex on side c whose neighbours greedily cover all existing vertices within distance D_. */
static int add_vertex(G *g, int c) {
    int n = g->n;
    if (n >= MAXN - 2) return 0;
    int W = (n + 63) / 64;
    balls(n, g, D_ - 1, BB);
    uint64_t U[MAXW];
    for (int w = 0; w < W; w++) U[w] = ~0ULL;
    if (n & 63) U[W - 1] = (1ULL << (n & 63)) - 1ULL;
    int chosen[DMAX], nch = 0;
    while (nch < d_) {
        int bestg = 0, bs = -1, ties = 0;
        for (int s = 0; s < n; s++) {
            if ((int)g->col[s] != 1 - c || g->deg[s] >= d_) continue;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += pc64(BB[s][w] & U[w]);
            if (gain > bestg) {
                bestg = gain;
                bs = s;
                ties = 1;
            } else if (gain == bestg && gain > 0) {
                ties++;
                if (rndi(ties) == 0) bs = s;
            }
        }
        if (bestg == 0) break;
        chosen[nch++] = bs;
        for (int w = 0; w < W; w++) U[w] &= ~BB[bs][w];
    }
    if (nch == 0) return 0;
    g->col[n] = (unsigned char)c;
    g->deg[n] = 0;
    g->n = n + 1;
    for (int i = 0; i < nch; i++) add_edge(g, chosen[i], n);
    return 1;
}

/* Delete the given vertices and compact the labels. */
static void remove_set(G *g, const int *kill, int k) {
    int n = g->n;
    for (int v = 0; v < n; v++) killed[v] = 0;
    for (int i = 0; i < k; i++) killed[kill[i]] = 1;
    for (int i = 0; i < k; i++) {
        int x = kill[i];
        for (int j = 0; j < g->deg[x]; j++) {
            int y = g->nb[x][j];
            if (!killed[y]) del_arc(g, y, x);
        }
    }
    int m = 0;
    for (int v = 0; v < n; v++) mapv[v] = killed[v] ? -1 : m++;
    tmpg.n = m;
    for (int v = 0; v < n; v++) {
        if (killed[v]) continue;
        int nv = mapv[v];
        tmpg.col[nv] = g->col[v];
        tmpg.deg[nv] = g->deg[v];
        for (int j = 0; j < g->deg[v]; j++) tmpg.nb[nv][j] = mapv[g->nb[v][j]];
    }
    copyg(g, &tmpg);
}

/* Simulated annealing over degree-preserving bipartite double-edge switches. */
static long long anneal(G *g, long long cur_c, int iters, double T0, double T1, double tend) {
    int n = g->n, n0 = 0;
    for (int v = 0; v < n; v++)
        if (g->col[v] == 0 && g->deg[v] > 0) L0[n0++] = v;
    if (n0 < 2 || cur_c == 0) return cur_c;
    double T = T0, alpha = pow(T1 / T0, 1.0 / iters);
    for (int it = 0; it < iters && cur_c > 0; it++) {
        if ((it & 31) == 0 && timeup(tend)) break;
        int a = L0[rndi(n0)], c = L0[rndi(n0)];
        if (a == c) {
            T *= alpha;
            continue;
        }
        int b = g->nb[a][rndi(g->deg[a])];
        int e = g->nb[c][rndi(g->deg[c])];
        if (b == e || has_edge(g, a, e) || has_edge(g, c, b)) {
            T *= alpha;
            continue;
        }
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long long nc = cost_of(g);
        if (nc <= cur_c || rndu() < exp(-(double)(nc - cur_c) / T)) {
            cur_c = nc;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
        T *= alpha;
    }
    return cur_c;
}

/* Greedily grow the current valid graph by one vertex while it stays valid. */
static void grow_phase(double tend) {
    int fails = 0;
    while (!timeup(tend) && fails < 40) {
        copyg(&work, &cur);
        int s = rndi(2);
        if (!add_vertex(&work, s) && !add_vertex(&work, 1 - s)) {
            fails++;
            continue;
        }
        fill(&work);
        if (cost_of(&work) == 0) {
            copyg(&cur, &work);
            if (cur.n > best.n) copyg(&best, &cur);
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* Kill-repair-regrow LNS on valid graphs. */
static void lns_phase(double tend) {
    while (!timeup(tend)) {
        int n = cur.n;
        if (n < 8) break;
        copyg(&work, &cur);
        int k = 1 + rndi(3);
        int kill[4], nk = 0;
        if (rndi(3) != 0) {
            kill[nk++] = rndi(n);
            for (int tries = 0; nk < k && tries < 60; tries++) {
                int x = kill[rndi(nk)];
                if (cur.deg[x] == 0) continue;
                int y = cur.nb[x][rndi(cur.deg[x])];
                int dup = 0;
                for (int i = 0; i < nk; i++)
                    if (kill[i] == y) dup = 1;
                if (!dup) kill[nk++] = y;
            }
        }
        while (nk < k) {
            int x = rndi(n), dup = 0;
            for (int i = 0; i < nk; i++)
                if (kill[i] == x) dup = 1;
            if (!dup) kill[nk++] = x;
        }
        remove_set(&work, kill, nk);
        int addn = nk + (rndi(4) == 0 ? 0 : 1);
        for (int j = 0; j < addn; j++) {
            int s = rndi(2);
            if (!add_vertex(&work, s)) add_vertex(&work, 1 - s);
        }
        if (work.n < cur.n) continue;
        fill(&work);
        long long c = cost_of(&work);
        c = anneal(&work, c, 300, 0.7, 0.05, tend);
        if (c == 0 && work.n >= cur.n) {
            copyg(&cur, &work);
            if (cur.n > best.n) copyg(&best, &cur);
        }
    }
}

static int init_kdd(void) {
    cur.n = 2 * d_;
    for (int v = 0; v < cur.n; v++) {
        cur.deg[v] = 0;
        cur.col[v] = (unsigned char)(v < d_ ? 0 : 1);
    }
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++)
            add_edge(&cur, i, d_ + j);
    return cost_of(&cur) == 0;
}

static int load_start(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n == 0) return init_kdd();
    if (n < 1 || n > MAXN - 64 || m < 0) return 0;
    cur.n = n;
    for (int v = 0; v < n; v++) {
        cur.deg[v] = 0;
        cur.col[v] = 0;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (cur.deg[u] >= d_ || cur.deg[v] >= d_) return 0;
        if (has_edge(&cur, u, v)) return 0;
        add_edge(&cur, u, v);
    }
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] != -1) continue;
        colr[s] = 0;
        int sp = 0;
        Lbuf[sp++] = s;
        while (sp > 0) {
            int x = Lbuf[--sp];
            for (int i = 0; i < cur.deg[x]; i++) {
                int y = cur.nb[x][i];
                if (colr[y] == -1) {
                    colr[y] = 1 - colr[x];
                    Lbuf[sp++] = y;
                }
            }
        }
    }
    for (int v = 0; v < n; v++) {
        cur.col[v] = (unsigned char)colr[v];
        for (int i = 0; i < cur.deg[v]; i++)
            if (colr[cur.nb[v][i]] == colr[v]) return 0;
    }
    return cost_of(&cur) == 0;
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
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double tend = (double)clock() + budget * CLOCKS_PER_SEC;
    if (d_ < 2 || d_ > DMAX - 1 || D_ < 2 || D_ > 20) {
        printf("0 0\n");
        return 0;
    }
    double s = 0, p = 1;
    for (int i = 0; i < D_; i++) {
        s += p;
        p *= (d_ - 1);
    }
    if (2 * s > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    if (!load_start()) {
        printf("0 0\n");
        return 0;
    }
    copyg(&best, &cur);
    grow_phase(tend);
    lns_phase(tend);
    print_graph(&best);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python graph helpers.
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
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized Python pipeline: mix twin duplication with cover growth and saturation."""
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
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.12 * time_limit, rng)
            consider(n1, e1)
    if best_n >= moore:
        return best_n, list(best_e)

    # Python randomized twin/grow pipelines produce a strong start for the C engine.
    trial_end = t0 + 0.2 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # Native C stage: two rounds, the second continuing from the best graph so far.
    for k in range(2):
        left = deadline - time.monotonic()
        if left < 1.5 or best_n >= moore:
            break
        budget = left * 0.6 if k == 0 else left - 0.5
        if budget < 1.0:
            break
        hard = time_limit - (time.monotonic() - t0) - 1.0
        timeout = max(1.0, min(budget * 1.5 + 3.0, hard))
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 2 + k, f"{budget:.2f}"],
                             stdin_graph=(best_n, best_e), timeout=timeout)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except Exception:
            break

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
