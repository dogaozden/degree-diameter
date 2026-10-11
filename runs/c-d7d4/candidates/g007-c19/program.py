import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on a valid bipartite graph (max degree d, diameter <= D). Each step adds
# a vertex on one side, joins it to a set of same-side vertices (evicting one
# edge at each full vertex), fills spare degree, and then anneals with
# degree-preserving bipartite double-edge switches to drive the number of bad
# pairs (distance > D) back to zero. Accepted states are always valid. Plateau
# walks with cost-0 switches diversify the valid state. Output is the largest
# valid graph seen, or "0 0" if none.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXDEG 32
#define MAXW ((MAXN + 63) / 64)

typedef uint64_t Row[MAXW];

static int d_, D_;
static int n_;
static int deg_[MAXN];
static int adj_[MAXN][MAXDEG];
static int col_[MAXN];
static Row bufA[MAXN], bufB[MAXN];

static int sn_;
static int sdeg_[MAXN];
static int sadj_[MAXN][MAXDEG];
static int scol_[MAXN];

static int bestn_;
static int bdeg_[MAXN];
static int badj_[MAXN][MAXDEG];

static uint64_t rs_ = 88172645463325252ULL;
static double t_start_, budget_;

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int time_up(void) { return now_s() - t_start_ >= budget_; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long cost_bad(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    Row *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj_[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        Row *t = cur; cur = nxt; nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        long c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        tot += (long)n - c;
    }
    return tot / 2;
}

static int find_idx(int v, int u) {
    for (int i = 0; i < deg_[v]; i++)
        if (adj_[v][i] == u) return i;
    return -1;
}
static int has_edge(int a, int b) { return find_idx(a, b) >= 0; }
static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}
static void del_edge(int a, int b) {
    int i = find_idx(a, b);
    adj_[a][i] = adj_[a][--deg_[a]];
    int j = find_idx(b, a);
    adj_[b][j] = adj_[b][--deg_[b]];
}
static void repl(int v, int old, int nw) {
    int i = find_idx(v, old);
    adj_[v][i] = nw;
}

static void save_best(void) {
    bestn_ = n_;
    for (int v = 0; v < n_; v++) {
        bdeg_[v] = deg_[v];
        memcpy(badj_[v], adj_[v], sizeof(int) * MAXDEG);
    }
}
static void maybe_record(void) {
    if (n_ > bestn_) save_best();
}
static void save_state(void) {
    sn_ = n_;
    for (int v = 0; v < n_; v++) {
        sdeg_[v] = deg_[v];
        scol_[v] = col_[v];
        memcpy(sadj_[v], adj_[v], sizeof(int) * MAXDEG);
    }
}
static void restore_state(void) {
    n_ = sn_;
    for (int v = 0; v < n_; v++) {
        deg_[v] = sdeg_[v];
        col_[v] = scol_[v];
        memcpy(adj_[v], sadj_[v], sizeof(int) * MAXDEG);
    }
}

/* Propose a bipartite double-edge switch a-b, c-e -> a-e, c-b (a,c side 0). */
static int propose(int *A, int *B, int *C, int *E) {
    int x = rndint(n_);
    if (deg_[x] == 0) return 0;
    int y = adj_[x][rndint(deg_[x])];
    int a, b, c, e;
    if (col_[x] == 0) { a = x; b = y; } else { a = y; b = x; }
    int z = rndint(n_);
    if (deg_[z] == 0) return 0;
    int w = adj_[z][rndint(deg_[z])];
    if (col_[z] == 0) { c = z; e = w; } else { c = w; e = z; }
    if (a == c || b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    *A = a; *B = b; *C = c; *E = e;
    return 1;
}
static void apply_switch(int a, int b, int c, int e) {
    repl(a, b, e);
    repl(e, c, a);
    repl(c, e, b);
    repl(b, a, c);
}
static void undo_switch(int a, int b, int c, int e) {
    repl(a, e, b);
    repl(e, a, c);
    repl(c, b, e);
    repl(b, c, a);
}

/* Add cross-side edges between deficient vertices (never increases distances). */
static void fill_edges(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (col_[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    if (n0 == 0 || n1 == 0) return;
    int fails = 0;
    while (n0 > 0 && n1 > 0 && fails < 50 + 4 * (n0 + n1)) {
        int i = rndint(n0), j = rndint(n1);
        int a = L0[i], b = L1[j];
        if (has_edge(a, b)) { fails++; continue; }
        add_edge(a, b);
        if (deg_[a] >= d_) L0[i] = L0[--n0];
        if (deg_[b] >= d_) L1[j] = L1[--n1];
    }
}

/* Add a new vertex on one side, joined to d_ vertices of the other side. */
static int add_vertex(void) {
    if (n_ >= MAXN - 2) return 0;
    int c = rndint(2);
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n_; u++)
        if (col_[u] == c) cand[nc++] = u;
    if (nc < d_) return 0;
    int v = n_;
    n_++;
    col_[v] = 1 - c;
    deg_[v] = 0;
    for (int k = 0; k < d_; k++) {
        int j = k + rndint(nc - k);
        int t = cand[k]; cand[k] = cand[j]; cand[j] = t;
        int s = cand[k];
        if (deg_[s] >= d_) {
            int t2 = adj_[s][rndint(deg_[s])];
            del_edge(s, t2);
        }
        add_edge(s, v);
    }
    return 1;
}

/* Metropolis annealing on bad-pair count. Returns final cost (0 means valid). */
static long anneal(int iters, double T0, double T1) {
    long cur = cost_bad();
    for (int it = 0; it < iters && cur > 0; it++) {
        if (time_up()) break;
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        long nc = cost_bad();
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nc;
        else undo_switch(a, b, c, e);
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    budget_ = atof(argv[4]);
    t_start_ = now_s();
    bestn_ = 0;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n > MAXN - 2 || d_ < 1 || d_ > MAXDEG || D_ < 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) deg_[v] = 0;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; continue; }
        if (deg_[u] >= MAXDEG || deg_[v] >= MAXDEG) { ok = 0; continue; }
        adj_[u][deg_[u]++] = v;
        adj_[v][deg_[v]++] = u;
    }
    if (!ok) { printf("0 0\n"); return 0; }
    n_ = n;
    for (int v = 0; v < n; v++) {
        col_[v] = -1;
        if (deg_[v] > d_) { printf("0 0\n"); return 0; }
    }
    /* Bipartition check. */
    {
        static int stk[MAXN];
        int bip = 1;
        for (int s = 0; s < n && bip; s++) {
            if (col_[s] != -1) continue;
            col_[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0 && bip) {
                int x = stk[--sp];
                for (int k = 0; k < deg_[x]; k++) {
                    int y = adj_[x][k];
                    if (col_[y] == -1) {
                        col_[y] = 1 - col_[x];
                        stk[sp++] = y;
                    } else if (col_[y] == col_[x]) {
                        bip = 0;
                    }
                }
            }
        }
        if (!bip) { printf("0 0\n"); return 0; }
    }
    if (cost_bad() != 0) { printf("0 0\n"); return 0; }
    save_best();
    save_state();

    while (!time_up()) {
        if (rndint(4) == 0) {
            /* Plateau walk: keep only cost-0 switches. */
            for (int t = 0; t < 30; t++) {
                int a, b, c, e;
                if (!propose(&a, &b, &c, &e)) continue;
                apply_switch(a, b, c, e);
                if (cost_bad() != 0) undo_switch(a, b, c, e);
            }
            fill_edges();
            save_state();
            maybe_record();
        } else {
            if (!add_vertex()) continue;
            fill_edges();
            long cc = anneal(1500, 2.0, 0.1);
            if (cc == 0) {
                fill_edges();
                save_state();
                maybe_record();
            } else {
                restore_state();
            }
        }
    }

    int E = 0;
    for (int v = 0; v < bestn_; v++)
        for (int k = 0; k < bdeg_[v]; k++)
            if (badj_[v][k] > v) E++;
    if (bestn_ == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestn_, E);
    for (int v = 0; v < bestn_; v++)
        for (int k = 0; k < bdeg_[v]; k++)
            if (badj_[v][k] > v) printf("%d %d\n", v, badj_[v][k]);
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

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin of v (same neighbourhood) is at distance
# 2 from v and at the same distance as v from all other vertices, so it never
# breaks the diameter bound.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
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
# Python kill-repair-regrow search (kept as a cheap pre-stage before C).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
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
        if not _anneal(adj, color, d, D, rng, 150, deadline):
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
# Build.
# ----------------------------------------------------------------------------

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
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Python kill-repair-regrow pre-stage.
    lns_end = start + 0.3 * time_limit
    if D >= 2 and time.monotonic() < lns_end:
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # C annealing stage: grow the best valid graph with bipartite switches.
    if (D >= 2 and d <= 31 and best_n < lib.moore_bound(d, D)
            and best_n <= 900):
        remaining = start + 0.92 * time_limit - time.monotonic() - 2.0
        if remaining > 4.0:
            budget = remaining - 1.5
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
