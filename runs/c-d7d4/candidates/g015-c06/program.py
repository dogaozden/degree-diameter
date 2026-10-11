import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine. Input: start graph on stdin ("n m" then m lines "u v", or
# "0 0"). Argv: d D seed budget_seconds. Output: best valid graph found.
#
# Moves: insert a vertex whose neighbourhood is a greedy cover of radius D-1
# balls (freeing degree by deleting edges where needed), or delete 1-3 random
# vertices. Each change is repaired by simulated annealing on double-edge
# switches (bipartite, degree-preserving), with cost = number of vertex pairs
# at distance > D (bitset balls). Only zero-cost states are accepted.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 4096
#define WMAX (CAP / 64)

static int d_, D_;
static uint64_t rs = 1;
static uint64_t *BUF[4];
static uint64_t COV[WMAX];
static int *F0, *F1, *S0, *STK;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

typedef struct { int n; int *deg; int *adj; unsigned char *col; } G;

static void g_init(G *g) {
    g->n = 0;
    g->deg = calloc(CAP, sizeof(int));
    g->adj = calloc((size_t)CAP * d_, sizeof(int));
    g->col = calloc(CAP, 1);
}

static void g_copy(G *dst, const G *src) {
    int n = src->n;
    dst->n = n;
    memcpy(dst->deg, src->deg, sizeof(int) * (size_t)n);
    memcpy(dst->adj, src->adj, sizeof(int) * (size_t)n * d_);
    memcpy(dst->col, src->col, (size_t)n);
}

static int has_edge(const G *g, int u, int v) {
    const int *a = g->adj + (size_t)u * d_;
    for (int k = 0; k < g->deg[u]; k++) if (a[k] == v) return 1;
    return 0;
}

static void add_edge(G *g, int u, int v) {
    g->adj[(size_t)u * d_ + g->deg[u]++] = v;
    g->adj[(size_t)v * d_ + g->deg[v]++] = u;
}

static void rem_one(G *g, int u, int v) {
    int *a = g->adj + (size_t)u * d_;
    int k = g->deg[u];
    for (int i = 0; i < k; i++) {
        if (a[i] == v) { a[i] = a[k - 1]; g->deg[u] = k - 1; return; }
    }
}

static void remove_edge(G *g, int u, int v) { rem_one(g, u, v); rem_one(g, v, u); }

/* Delete vertex v; the last vertex is moved into slot v. */
static void del_vertex(G *g, int v) {
    while (g->deg[v] > 0) remove_edge(g, v, g->adj[(size_t)v * d_]);
    int last = g->n - 1;
    if (v != last) {
        while (g->deg[last] > 0) {
            int u = g->adj[(size_t)last * d_];
            remove_edge(g, last, u);
            add_edge(g, v, u);
        }
        g->col[v] = g->col[last];
    }
    g->n--;
}

/* Bitset balls of radius r; result is one of A or B. */
static uint64_t *balls(const G *g, int r, uint64_t *A, uint64_t *B) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *cur = A, *nxt = B;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + (size_t)v * W;
            memcpy(x, cur + (size_t)v * W, sizeof(uint64_t) * W);
            const int *a = g->adj + (size_t)v * d_;
            int k = g->deg[v];
            for (int j = 0; j < k; j++) {
                const uint64_t *y = cur + (size_t)a[j] * W;
                for (int w = 0; w < W; w++) x[w] |= y[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered vertex pairs at distance > D_. */
static long long cost_g(const G *g) {
    int n = g->n, W = (n + 63) >> 6;
    uint64_t *R = balls(g, D_, BUF[0], BUF[1]);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *x = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(x[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add edges between deficient opposite-side vertices (only helps distances). */
static void fill_g(G *g) {
    int n = g->n, m0 = 0, m1 = 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] < d_) {
            if (g->col[v] == 0) F0[m0++] = v; else F1[m1++] = v;
        }
    }
    for (int i = m0 - 1; i > 0; i--) { int j = rndint(i + 1); int t = F0[i]; F0[i] = F0[j]; F0[j] = t; }
    for (int i = m1 - 1; i > 0; i--) { int j = rndint(i + 1); int t = F1[i]; F1[i] = F1[j]; F1[j] = t; }
    for (int i = 0; i < m0; i++) {
        int a = F0[i];
        for (int j = 0; j < m1 && g->deg[a] < d_; j++) {
            int b = F1[j];
            if (g->deg[b] < d_ && !has_edge(g, a, b)) add_edge(g, a, b);
        }
    }
}

/* Insert a new vertex on side c, adjacent to a greedy cover of radius D-1 balls. */
static int insert_cover(G *g, int c) {
    int n = g->n;
    if (n >= CAP - 1) return 0;
    int W = (n + 63) >> 6;
    uint64_t *R = balls(g, D_ - 1, BUF[2], BUF[3]);
    memset(COV, 0, sizeof(uint64_t) * W);
    int *chosen = malloc(sizeof(int) * (size_t)(d_ + 1));
    int nc = 0;
    for (int p = 0; p < d_; p++) {
        int best = -1, bg = 0, ties = 0;
        for (int s = 0; s < n; s++) {
            if (g->col[s] == c) continue;
            const uint64_t *x = R + (size_t)s * W;
            int gain = 0;
            for (int w = 0; w < W; w++) gain += __builtin_popcountll(x[w] & ~COV[w]);
            if (gain > bg) { bg = gain; best = s; ties = 1; }
            else if (gain == bg && gain > 0) { ties++; if (rndint(ties) == 0) best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        const uint64_t *x = R + (size_t)best * W;
        for (int w = 0; w < W; w++) COV[w] |= x[w];
    }
    if (nc == 0) { free(chosen); return 0; }
    int v = n;
    g->n = n + 1;
    g->col[v] = (unsigned char)c;
    g->deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (g->deg[s] >= d_) {
            int w = g->adj[(size_t)s * d_ + rndint(g->deg[s])];
            remove_edge(g, s, w);
        }
    }
    for (int i = 0; i < nc; i++) add_edge(g, v, chosen[i]);
    free(chosen);
    return 1;
}

/* Degree-preserving bipartite double-edge switches minimising cost. Returns 1 on cost 0. */
static int anneal(G *g, int iters, double T0, double T1) {
    int n = g->n, m0 = 0;
    for (int v = 0; v < n; v++) if (g->col[v] == 0) S0[m0++] = v;
    if (m0 == 0 || n < 2) return cost_g(g) == 0;
    fill_g(g);
    long long cur = cost_g(g);
    if (cur == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 255) {
            fill_g(g);
            cur = cost_g(g);
            if (cur == 0) return 1;
        }
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a = S0[rndint(m0)];
        if (g->deg[a] == 0) continue;
        int b = g->adj[(size_t)a * d_ + rndint(g->deg[a])];
        int c = S0[rndint(m0)];
        if (c == a || g->deg[c] == 0) continue;
        int e = g->adj[(size_t)c * d_ + rndint(g->deg[c])];
        if (has_edge(g, a, e) || has_edge(g, c, b)) continue;
        remove_edge(g, a, b);
        remove_edge(g, c, e);
        add_edge(g, a, e);
        add_edge(g, c, b);
        long long nw = cost_g(g);
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            remove_edge(g, a, e);
            remove_edge(g, c, b);
            add_edge(g, a, b);
            add_edge(g, c, e);
        }
        if (cur == 0) return 1;
    }
    return 0;
}

/* Replace with K_{d,d}: valid for D >= 2. */
static void set_kdd(G *g) {
    memset(g->deg, 0, sizeof(int) * CAP);
    g->n = 2 * d_;
    for (int v = 0; v < 2 * d_; v++) g->col[v] = (v < d_) ? 0 : 1;
    for (int u = 0; u < d_; u++)
        for (int v = d_; v < 2 * d_; v++) add_edge(g, u, v);
}

static void print_graph(const G *g) {
    long long m = 0;
    for (int v = 0; v < g->n; v++) m += g->deg[v];
    m /= 2;
    printf("%d %lld\n", g->n, m);
    for (int v = 0; v < g->n; v++)
        for (int k = 0; k < g->deg[v]; k++) {
            int u = g->adj[(size_t)v * d_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: prog d D seed budget\n"); return 1; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 1) d_ = 1;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rs) rs = 1;

    double t0 = now_s();
    double deadline = t0 + budget;

    for (int i = 0; i < 4; i++) BUF[i] = calloc((size_t)CAP * WMAX, sizeof(uint64_t));
    F0 = malloc(sizeof(int) * CAP);
    F1 = malloc(sizeof(int) * CAP);
    S0 = malloc(sizeof(int) * CAP);
    STK = malloc(sizeof(int) * CAP);

    G cur, best, work;
    g_init(&cur);
    g_init(&best);
    g_init(&work);

    int n0 = 0, m0 = 0, okin = 1;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || n0 > CAP - 2) okin = 0;
    int have = 0;
    if (okin && n0 > 0) {
        cur.n = n0;
        for (int i = 0; i < m0 && okin; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { okin = 0; break; }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { okin = 0; break; }
            if (cur.deg[u] >= d_ || cur.deg[v] >= d_ || has_edge(&cur, u, v)) { okin = 0; break; }
            add_edge(&cur, u, v);
        }
        if (okin) {
            for (int v = 0; v < n0; v++) cur.col[v] = 255;
            for (int s = 0; s < n0 && okin; s++) {
                if (cur.col[s] != 255) continue;
                cur.col[s] = 0;
                int sp = 0;
                STK[sp++] = s;
                while (sp > 0 && okin) {
                    int x = STK[--sp];
                    for (int k = 0; k < cur.deg[x]; k++) {
                        int y = cur.adj[(size_t)x * d_ + k];
                        if (cur.col[y] == 255) { cur.col[y] = (unsigned char)(1 - cur.col[x]); STK[sp++] = y; }
                        else if (cur.col[y] == cur.col[x]) { okin = 0; break; }
                    }
                }
            }
        }
        if (okin && cost_g(&cur) == 0) have = 1;
    }
    if (!have) set_kdd(&cur);

    g_copy(&best, &cur);

    int ITG = 3000, ITK = 3000;
    while (now_s() < deadline) {
        int op = rndint(100);
        g_copy(&work, &cur);
        int success = 0;
        if (op < 65 || work.n < 4) {
            int c = rndint(2);
            if (!insert_cover(&work, c)) continue;
            success = anneal(&work, ITG, 0.8, 0.05);
        } else {
            int k = 1 + rndint(3);
            for (int i = 0; i < k && work.n > 2; i++) del_vertex(&work, rndint(work.n));
            fill_g(&work);
            success = anneal(&work, ITK, 0.8, 0.05);
        }
        if (success) {
            g_copy(&cur, &work);
            if (cur.n > best.n) g_copy(&best, &cur);
        }
        if (cur.n + 3 < best.n) g_copy(&cur, &best);
    }

    if (cost_g(&best) != 0) set_kdd(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and glue.
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Python phase: structured base, cover growth, twin duplication.
    if D >= 2:
        base = None
        if D >= 4:
            base = _best_gq(d)
        if base is None and D >= 3:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)
        for _ in range(4):
            if time.monotonic() > start + 0.14 * time_limit:
                break
            n2, e2 = _duplicate_twins(best_n, list(best_e), d, rng)
            n2, e2 = _grow(n2, e2, d, D, start + 0.16 * time_limit, rng)
            consider(n2, e2)

    # C phase: annealed insert/delete search from the best graph so far.
    total_end = start + 0.92 * time_limit
    if D >= 2 and best_n < lib.moore_bound(d, D):
        remaining = total_end - time.monotonic()
        if remaining > 5.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 3.0, 2)],
                                stdin_graph=(best_n, best_e), timeout=remaining)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
