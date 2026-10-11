import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-based simulated annealing with vertex insertion.
# Starts from a valid bipartite graph, repeatedly adds a vertex whose
# neighbourhood covers the graph within distance D-1, repairs the diameter
# with degree-preserving double-edge switches, and keeps only valid results.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXDEG 64
#define MAXW 25

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXDEG];
} Graph;

static Graph CUR, WORK;
static int DIAM = 4;
static uint64_t RS = 88172645463325252ULL;
static uint64_t BALL[MAXN][MAXW];
static uint64_t TMPB[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(const Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++)
        if (g->adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(Graph *g, int a, int b) {
    g->adj[a][g->deg[a]++] = b;
    g->adj[b][g->deg[b]++] = a;
}

static void del_arc(Graph *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) {
        if (g->adj[a][i] == b) {
            g->deg[a]--;
            g->adj[a][i] = g->adj[a][g->deg[a]];
            return;
        }
    }
}

static void del_edge(Graph *g, int a, int b) {
    del_arc(g, a, b);
    del_arc(g, b, a);
}

/* R[v] = bitmask of all vertices within distance r of v. */
static void balls(const Graph *g, int r, uint64_t (*R)[MAXW]) {
    int n = g->n, W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) R[v][w] = 0;
        R[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < r; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) TMPB[v][w] = R[v][w];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                for (int w = 0; w < W; w++) TMPB[v][w] |= R[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) R[v][w] = TMPB[v][w];
    }
}

/* Number of unordered vertex pairs at distance more than DIAM. */
static long cost_of(const Graph *g) {
    int n = g->n, W = (n + 63) >> 6;
    balls(g, DIAM, RB);
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(RB[v][w]);
        tot += n - cnt;
    }
    return tot / 2;
}

/* Append a vertex on the side opposite to `side`, joined to a greedy cover
   of the old vertices by balls of radius DIAM-1 around chosen vertices of `side`. */
static void add_vertex(Graph *g, int side, int d) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t covered[MAXW];
    int chosen[MAXDEG];
    int nc = 0;
    balls(g, DIAM - 1, BALL);
    for (int w = 0; w < W; w++) covered[w] = 0;
    for (int k = 0; k < d; k++) {
        int best = -1;
        long bestsc = -1;
        for (int x = 0; x < n; x++) {
            if (g->col[x] != side) continue;
            int used = 0;
            for (int i = 0; i < nc; i++)
                if (chosen[i] == x) { used = 1; break; }
            if (used) continue;
            int gain = 0;
            for (int w = 0; w < W; w++)
                gain += pc64(BALL[x][w] & ~covered[w]);
            long sc = (long)gain * 4 + (g->deg[x] < d ? 2 : 0) + rndi(3);
            if (sc > bestsc) { bestsc = sc; best = x; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= BALL[best][w];
    }
    int v = n;
    g->n = n + 1;
    g->deg[v] = 0;
    g->col[v] = 1 - side;
    for (int i = 0; i < nc; i++) {
        int x = chosen[i];
        if (g->deg[x] >= d) {
            int y = g->adj[x][rndi(g->deg[x])];
            del_edge(g, x, y);
        }
        add_edge(g, x, v);
    }
}

/* Join deficient opposite-side vertices (only shortens distances). */
static void fill_deficient(Graph *g, int d) {
    int n = g->n;
    static int LL[MAXN], RR[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] >= d) continue;
        if (g->col[v] == 0) LL[nl++] = v;
        else RR[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = LL[i]; LL[i] = LL[j]; LL[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = RR[i]; RR[i] = RR[j]; RR[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = LL[i];
        for (int j = 0; j < nr; j++) {
            if (g->deg[a] >= d) break;
            int b = RR[j];
            if (g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
        }
    }
}

/* Degree-preserving double-edge switches minimising the bad-pair cost. */
static long anneal(Graph *g, long iters, double T, long cur, double tend) {
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > tend) break;
        int n = g->n;
        int a = rndi(n);
        if (g->deg[a] == 0) continue;
        int b = g->adj[a][rndi(g->deg[a])];
        int c = rndi(n);
        if (c == a || g->col[c] != g->col[a] || g->deg[c] == 0) continue;
        int e = g->adj[c][rndi(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        del_edge(g, a, b);
        del_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long nc = cost_of(g);
        int accept = (nc <= cur);
        if (!accept && T > 0.0) {
            double p = exp(-(double)(nc - cur) / T);
            accept = (rndu() < p);
        }
        if (accept) {
            cur = nc;
        } else {
            del_edge(g, a, e);
            del_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
    }
    return cur;
}

/* Reads "n m" and edges; returns 0 on any violation (degree, duplicate, odd cycle). */
static int read_graph(Graph *g, int d) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN || m < 0) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->col[v] = -1;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (g->deg[u] >= d || g->deg[v] >= d) return 0;
        if (has_edge(g, u, v)) return 0;
        add_edge(g, u, v);
    }
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->col[s] != -1) continue;
        g->col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
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
    long m = 0;
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) m++;
    printf("%d %ld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int i = 0; i < g->deg[v]; i++)
            if (g->adj[v][i] > v) printf("%d %d\n", v, g->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    RS = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    if (RS == 0) RS = 1;
    double tl = atof(argv[4]);
    long iters = argc > 5 ? atol(argv[5]) : 6000;
    double T = argc > 6 ? atof(argv[6]) : 0.6;
    if (d < 1 || d > MAXDEG || DIAM < 1) { printf("0 0\n"); return 0; }
    double tend = now() + tl;
    if (!read_graph(&CUR, d)) { printf("0 0\n"); return 0; }
    fill_deficient(&CUR, d);
    long c = cost_of(&CUR);
    while (c > 0 && now() < tend)
        c = anneal(&CUR, iters, T, c, tend);
    if (c > 0) { printf("0 0\n"); return 0; }
    while (now() < tend && CUR.n < MAXN) {
        WORK = CUR;
        add_vertex(&WORK, rndi(2), d);
        fill_deficient(&WORK, d);
        long wc = cost_of(&WORK);
        wc = anneal(&WORK, iters, T, wc, tend);
        if (wc == 0) CUR = WORK;
    }
    print_graph(&CUR);
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


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 9)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _base(d, D):
    """Structured starting graph: W(q) for D >= 4, PG(2, q) for D = 3, else None."""
    if D >= 4:
        b = _best_gq(d)
        if b is not None:
            return b
    if D >= 3:
        return _best_pg(d)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers (growth, twins, group lifts).
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidates. Returns list or None."""
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
    """Greedily add vertices whose neighbourhoods cover the vertices at distance D-1."""
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
    """Greedily join deficient opposite-side vertices in random order. Only shortens distances."""
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    if order < 2:
        return None
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _group_phase(d, D, best, rng, deadline, consider):
    """Adaptive group-lift search; `best` is a dict holding the current best 'n'."""
    group_sizes = [1, 2, 3, 4]
    state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    while time.monotonic() < deadline:
        k = rng.choice(group_sizes)
        st = state[k]
        floor = best["n"] // (2 * k) + 1
        G = max(st["G"], floor, 2)
        res = _group_search(d, D, k, G, rng, 200, deadline)
        if res is not None:
            consider(res[0], res[1])
            st["G"] = G + st["step"]
            st["step"] = min(st["step"] * 2, max(1, G // 10))
            st["miss"] = 0
        else:
            st["G"] = G
            st["miss"] += 1
            if st["miss"] >= 3:
                st["step"] = 1
                st["miss"] = 0
                st["G"] = floor


# ----------------------------------------------------------------------------
# Main build: short Python construction stage, then C annealing growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": list(fb_e)}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    consider(fb_n, fb_e)

    # Structured base (W(q) for D >= 4, PG(2,q) for D = 3), then cover growth.
    base_n, base_e = best["n"], list(best["e"])
    base = _base(d, D)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        n0, e0 = base
        base_n, base_e = n0, list(e0)
        consider(n0, e0)
        n1, e1 = _grow(n0, e0, d, D, t0 + 0.12 * time_limit, rng)
        consider(n1, e1)

    # Group-lift family (mainly for D >= 4).
    if D >= 4:
        _group_phase(d, D, best, rng, t0 + 0.20 * time_limit, consider)

    # Randomized twin / growth pipelines.
    if D >= 2:
        trial_end = t0 + 0.30 * time_limit
        while time.monotonic() < trial_end:
            if rng.random() < 0.5:
                src_n, src_e = base_n, base_e
            else:
                src_n, src_e = best["n"], best["e"]
            n, e = _trial(src_n, src_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing growth from the best valid graph found so far.
    elapsed = time.monotonic() - t0
    budget = 0.78 * time_limit - elapsed - 1.5
    if budget >= 2.0 and best["n"] >= 2:
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, int(seed) & 0xFFFFFFFF, round(budget, 2), 6000, 0.6],
                stdin_graph=(best["n"], best["e"]),
                timeout=budget + 10.0,
            )
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best["n"], best["e"], d, D):
        return lib.haar_graph(d, range(d))
    return best["n"], list(best["e"])
