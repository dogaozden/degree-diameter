import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite simulated annealing on bad-pair cost, with vertex growth.
# State: a valid bipartite graph (degree <= d, diameter <= D). Growth adds a
# vertex joined to d opposite-side vertices (saturated ones lose a random edge);
# annealing uses degree-preserving bipartite double-edge switches and
# degree-increasing edge additions to drive the number of pairs at distance > D
# to zero. Only zero-cost states are kept, so every output is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 576
#define WD 9
#define MAXD 64

typedef uint64_t u64;

typedef struct {
    int n;
    int col[MAXN];
    int deg[MAXN];
    int nb[MAXN][MAXD];
    u64 mat[MAXN][WD];
} G;

static G base_g, work_g, best_g;
static int DEG, DIAM;
static u64 rs = 88172645463325252ULL;
static clock_t deadline_clk;
static u64 BA[MAXN][WD], BB[MAXN][WD];

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return clock() >= deadline_clk; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const G *g, int a, int b) {
    return (int)((g->mat[a][b >> 6] >> (b & 63)) & 1ULL);
}

static void add_edge(G *g, int a, int b) {
    g->nb[a][g->deg[a]++] = b;
    g->nb[b][g->deg[b]++] = a;
    g->mat[a][b >> 6] |= 1ULL << (b & 63);
    g->mat[b][a >> 6] |= 1ULL << (a & 63);
}

static void drop(int *arr, int *len, int x) {
    for (int i = 0; i < *len; i++) {
        if (arr[i] == x) { arr[i] = arr[*len - 1]; (*len)--; return; }
    }
}

static void rem_edge(G *g, int a, int b) {
    drop(g->nb[a], &g->deg[a], b);
    drop(g->nb[b], &g->deg[b], a);
    g->mat[a][b >> 6] &= ~(1ULL << (b & 63));
    g->mat[b][a >> 6] &= ~(1ULL << (a & 63));
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Number of ordered-once unordered pairs at distance > DIAM (unreachable counts). */
static long long cost_of(const G *g) {
    int n = g->n, nw = (n + 63) >> 6;
    u64 (*X)[WD] = BA, (*Y)[WD] = BB, (*T)[WD];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < g->deg[v]; k++) {
                int u = g->nb[v][k];
                for (int w = 0; w < nw; w++) Y[v][w] |= X[u][w];
            }
        }
        T = X; X = Y; Y = T;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += pc64(X[v][w]);
        tot += n - c;
    }
    return tot / 2;
}

static int pick_switch(const G *g, int *pa, int *pb, int *pc, int *pe) {
    int n = g->n, a = -1, c = -1;
    for (int tr = 0; tr < 60 && (a < 0 || c < 0); tr++) {
        int x = rndint(n);
        if (g->col[x] == 0 && g->deg[x] > 0) {
            if (a < 0) a = x;
            else if (c < 0 && x != a) c = x;
        }
    }
    if (a < 0 || c < 0) return 0;
    int b = g->nb[a][rndint(g->deg[a])];
    int e = g->nb[c][rndint(g->deg[c])];
    if (b == e || has_edge(g, a, e) || has_edge(g, c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static void apply_switch(G *g, int a, int b, int c, int e) {
    rem_edge(g, a, b); rem_edge(g, c, e);
    add_edge(g, a, e); add_edge(g, c, b);
}

static void undo_switch(G *g, int a, int b, int c, int e) {
    rem_edge(g, a, e); rem_edge(g, c, b);
    add_edge(g, a, b); add_edge(g, c, e);
}

static void perturb(G *g, int k) {
    for (int it = 0; it < k; it++) {
        int a, b, c, e;
        if (pick_switch(g, &a, &b, &c, &e)) apply_switch(g, a, b, c, e);
    }
}

/* Simulated annealing at fixed n. Returns 1 if cost reached 0 (state valid). */
static int anneal(G *g, long long *costp, long long iters, double T0, double T1) {
    long long cost = *costp;
    int n = g->n;
    for (long long it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (rnd01() < 0.08) {
            int x = rndint(n), y = rndint(n);
            if (g->col[x] != 0) { int t = x; x = y; y = t; }
            if (g->col[x] == 0 && g->col[y] == 1 && g->deg[x] < DEG &&
                g->deg[y] < DEG && !has_edge(g, x, y)) {
                add_edge(g, x, y);
                cost = cost_of(g);
            }
            continue;
        }
        int a, b, c, e;
        if (!pick_switch(g, &a, &b, &c, &e)) continue;
        apply_switch(g, a, b, c, e);
        long long nc = cost_of(g);
        long long delta = nc - cost;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cost = nc;
        else undo_switch(g, a, b, c, e);
    }
    *costp = cost;
    return cost == 0;
}

/* Add one vertex on the smaller side, joined to DEG opposite-side vertices. */
static int grow_one(G *g) {
    if (g->n >= MAXN - 1) return 0;
    int c0 = 0, c1 = 0;
    for (int v = 0; v < g->n; v++) { if (g->col[v]) c1++; else c0++; }
    int c = (c0 <= c1) ? 0 : 1;
    int opp = 1 - c;
    static int spare[MAXN], full_[MAXN];
    int ns = 0, nf = 0;
    for (int u = 0; u < g->n; u++) {
        if (g->col[u] != opp) continue;
        if (g->deg[u] < DEG) spare[ns++] = u;
        else full_[nf++] = u;
    }
    shuffle_int(spare, ns);
    shuffle_int(full_, nf);
    int chosen[MAXD], nc = 0;
    for (int i = 0; i < ns && nc < DEG; i++) chosen[nc++] = spare[i];
    for (int i = 0; i < nf && nc < DEG; i++) chosen[nc++] = full_[i];
    if (nc < DEG) return 0;
    int v = g->n++;
    g->col[v] = c;
    g->deg[v] = 0;
    memset(g->mat[v], 0, sizeof g->mat[v]);
    for (int k = 0; k < nc; k++) {
        int u = chosen[k];
        if (g->deg[u] >= DEG) {
            int w = g->nb[u][rndint(g->deg[u])];
            rem_edge(g, u, w);
        }
        add_edge(g, v, u);
    }
    return 1;
}

static void make_kdd(void) {
    memset(&base_g, 0, sizeof base_g);
    int k = DEG;
    base_g.n = 2 * k;
    for (int i = 0; i < k; i++) { base_g.col[i] = 0; base_g.col[k + i] = 1; }
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            add_edge(&base_g, i, k + j);
}

static int load_graph(int n, int m) {
    memset(&base_g, 0, sizeof base_g);
    base_g.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(&base_g, u, v)) return 0;
        if (base_g.deg[u] >= DEG || base_g.deg[v] >= DEG) return 0;
        add_edge(&base_g, u, v);
    }
    for (int v = 0; v < n; v++) base_g.col[v] = -1;
    int q[MAXN];
    for (int s = 0; s < n; s++) {
        if (base_g.col[s] != -1) continue;
        base_g.col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int k = 0; k < base_g.deg[x]; k++) {
                int y = base_g.nb[x][k];
                if (base_g.col[y] == -1) {
                    base_g.col[y] = 1 - base_g.col[x];
                    q[t++] = y;
                } else if (base_g.col[y] == base_g.col[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    clock_t t0 = clock();
    deadline_clk = t0 + (clock_t)(budget * CLOCKS_PER_SEC);
    if (DEG < 1 || DEG > MAXD - 2 || DIAM < 1) { printf("0 0\n"); return 0; }

    int n_in = 0, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) { n_in = 0; m_in = 0; }
    if (n_in == 0) {
        make_kdd();
    } else {
        if (n_in < 1 || n_in > MAXN - 2 || m_in < 0 || !load_graph(n_in, m_in)) {
            printf("0 0\n");
            return 0;
        }
    }

    long long c0 = cost_of(&base_g);
    if (c0 != 0) {
        clock_t saved = deadline_clk;
        clock_t rep = t0 + (clock_t)(0.2 * budget * CLOCKS_PER_SEC);
        if (rep < saved) deadline_clk = rep;
        while (c0 != 0 && !timeup()) anneal(&base_g, &c0, 4000, 1.0, 0.05);
        deadline_clk = saved;
        if (c0 != 0) { printf("0 0\n"); return 0; }
    }

    best_g = base_g;
    int fails = 0;
    static const double T0s[4] = {0.5, 1.0, 2.0, 3.0};
    while (!timeup()) {
        work_g = base_g;
        int grew = 0;
        if (rnd01() < 0.75) grew = grow_one(&work_g);
        if (!grew) perturb(&work_g, 6 + rndint(30));
        long long cost = cost_of(&work_g);
        double T0 = T0s[rndint(4)];
        int boost = fails / 20;
        if (boost > 10) boost = 10;
        long long iters = 4000 + 4000LL * boost;
        if (anneal(&work_g, &cost, iters, T0, 0.05)) {
            base_g = work_g;
            fails = 0;
            if (base_g.n > best_g.n) best_g = base_g;
        } else {
            fails++;
        }
    }

    int m = 0;
    for (int v = 0; v < best_g.n; v++) m += best_g.deg[v];
    m /= 2;
    printf("%d %d\n", best_g.n, m);
    for (int v = 0; v < best_g.n; v++)
        for (int k = 0; k < best_g.deg[v]; k++) {
            int u = best_g.nb[v][k];
            if (v < u) printf("%d %d\n", v, u);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (Python).
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for the structured start graph.
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidate vertices. Returns list or None."""
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
    """Add vertices whose neighbourhoods cover all vertices within distance D - 1."""
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
            for attempt in range(40):
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
    """Join deficient opposite-side vertices in random order. Keeps validity."""
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


# ----------------------------------------------------------------------------
# Driver: structured start (Python, short), then C annealing growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.85 * time_limit
    end = t0 + total
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured start: W(q) for D >= 4, PG(2, q) for D = 3, grown by covers.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, t0 + 0.12 * total, rng)
            consider(n1, e1)

    # C stage: anneal-and-grow from the best valid graph so far.
    if D >= 2 and best_n < lib.moore_bound(d, D):
        remaining = end - time.monotonic()
        if remaining > 4:
            budget = remaining - 1.5  # reserve time for compilation
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=remaining + 2.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
