import itertools
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
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 32

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXDEG];
} State;

typedef struct {
    int nr, na;
    int ru[2], rv[2], au[2], av[2];
} Move;

static State cur, best, snap;
static int d_, D_;
static double deadline_s;
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rng_s = 88172645463325252ULL;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset balls of radius r around every vertex; returns pointer to buffer holding them. */
static uint64_t *balls(int r) {
    int n = cur.n, W = (n + 63) / 64;
    uint64_t *c = bufA, *nx = bufB;
    memset(c, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) c[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * W;
            const uint64_t *cv = c + (size_t)v * W;
            memcpy(o, cv, sizeof(uint64_t) * W);
            for (int i = 0; i < cur.deg[v]; i++) {
                const uint64_t *x = c + (size_t)cur.adj[v][i] * W;
                for (int k = 0; k < W; k++) o[k] |= x[k];
            }
        }
        uint64_t *t = c; c = nx; nx = t;
    }
    return c;
}

/* Number of unordered vertex pairs at distance > D_. */
static long long cost_now(void) {
    int n = cur.n, W = (n + 63) / 64;
    uint64_t *b = balls(D_);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < W; k++) c += popc64(b[(size_t)v * W + k]);
        tot += n - c;
    }
    return tot / 2;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) if (cur.adj[u][i] == v) return 1;
    return 0;
}
static void del_half(int u, int v) {
    for (int i = 0; i < cur.deg[u]; i++) {
        if (cur.adj[u][i] == v) {
            cur.adj[u][i] = cur.adj[u][--cur.deg[u]];
            return;
        }
    }
}
static void add_edge(int u, int v) {
    cur.adj[u][cur.deg[u]++] = v;
    cur.adj[v][cur.deg[v]++] = u;
}
static void remove_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 8 || m < 0) return 0;
    memset(&cur, 0, sizeof cur);
    cur.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (cur.deg[u] >= d_ || cur.deg[v] >= d_) return 0;
        if (has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int col[MAXN], qq[MAXN];
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        qq[t++] = s;
        while (h < t) {
            int u = qq[h++];
            for (int i = 0; i < cur.deg[u]; i++) {
                int v = cur.adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    qq[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) cur.side[i] = col[i];
    return 1;
}

static void make_kdd(void) {
    memset(&cur, 0, sizeof cur);
    cur.n = 2 * d_;
    for (int i = 0; i < d_; i++) {
        cur.side[i] = 0;
        cur.side[d_ + i] = 1;
    }
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++) add_edge(i, d_ + j);
}

static int rand_side(int s) {
    for (int t = 0; t < 400; t++) {
        int v = rndint(cur.n);
        if (cur.side[v] == s) return v;
    }
    return -1;
}

/* Random local move: degree-preserving switch, edge add, endpoint move, or edge removal. */
static int propose(Move *m) {
    int r = rndint(7);
    m->nr = m->na = 0;
    if (r < 3) {
        int a = rand_side(0);
        if (a < 0 || cur.deg[a] == 0) return 0;
        int b = cur.adj[a][rndint(cur.deg[a])];
        int c = rand_side(0);
        if (c < 0 || c == a || cur.deg[c] == 0) return 0;
        int e = cur.adj[c][rndint(cur.deg[c])];
        if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
        m->nr = 2;
        m->ru[0] = a; m->rv[0] = b; m->ru[1] = c; m->rv[1] = e;
        m->na = 2;
        m->au[0] = a; m->av[0] = e; m->au[1] = c; m->av[1] = b;
        return 1;
    }
    if (r == 3) {
        int a = rand_side(0), b = rand_side(1);
        if (a < 0 || b < 0) return 0;
        if (cur.deg[a] >= d_ || cur.deg[b] >= d_ || has_edge(a, b)) return 0;
        m->na = 1;
        m->au[0] = a; m->av[0] = b;
        return 1;
    }
    if (r < 6) {
        int a = rand_side(0);
        if (a < 0 || cur.deg[a] == 0) return 0;
        int b = cur.adj[a][rndint(cur.deg[a])];
        m->nr = 1;
        m->ru[0] = a; m->rv[0] = b;
        if (rndint(2)) {
            int e = rand_side(1);
            if (e < 0 || e == b || cur.deg[e] >= d_ || has_edge(a, e)) return 0;
            m->na = 1;
            m->au[0] = a; m->av[0] = e;
        } else {
            int c = rand_side(0);
            if (c < 0 || c == a || cur.deg[c] >= d_ || has_edge(c, b)) return 0;
            m->na = 1;
            m->au[0] = c; m->av[0] = b;
        }
        return 1;
    }
    int a = rand_side(0);
    if (a < 0 || cur.deg[a] == 0) return 0;
    m->nr = 1;
    m->ru[0] = a; m->rv[0] = cur.adj[a][rndint(cur.deg[a])];
    return 1;
}

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) remove_edge(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_edge(m->au[i], m->av[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) remove_edge(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_edge(m->ru[i], m->rv[i]);
}

/* Simulated annealing on bad-pair count. Returns 1 when the state becomes valid. */
static int anneal(int iters, double T0, double T1) {
    long long c = cost_now();
    if (c == 0) return 1;
    for (int it = 0; it < iters; it++) {
        if ((it & 255) == 255 && now_s() > deadline_s) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Move m;
        if (!propose(&m)) continue;
        apply_move(&m);
        long long c2 = cost_now();
        long long dl = c2 - c;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            undo_move(&m);
        }
    }
    return 0;
}

/* Plateau walk: only moves that keep the state valid are kept. */
static void walk(int iters) {
    for (int it = 0; it < iters; it++) {
        Move m;
        if (!propose(&m)) continue;
        apply_move(&m);
        if (cost_now() != 0) undo_move(&m);
    }
}

/* Adding cross-side edges never breaks validity; saturate deficient pairs. */
static void fill(void) {
    int n = cur.n;
    for (int a = 0; a < n; a++) {
        if (cur.side[a] != 0 || cur.deg[a] >= d_) continue;
        for (int b = 0; b < n && cur.deg[a] < d_; b++) {
            if (cur.side[b] != 1 || cur.deg[b] >= d_ || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* New vertex joined to a greedy cover (by radius D-1 balls) of the opposite side. */
static void add_vertex(void) {
    int n = cur.n, W = (n + 63) / 64;
    uint64_t *B = balls(D_ - 1);
    uint64_t U[MAXW];
    memset(U, 0, sizeof U);
    for (int v = 0; v < n; v++) U[v / 64] |= 1ULL << (v % 64);
    int chosen[MAXDEG];
    int nc = 0;
    int t = rndint(2), want = 1 - t;
    for (int step = 0; step < d_; step++) {
        int bx = -1;
        long long bs = -1;
        for (int x = 0; x < n; x++) {
            if (cur.side[x] != want) continue;
            int used = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == x) { used = 1; break; }
            if (used) continue;
            const uint64_t *row = B + (size_t)x * W;
            int c = 0;
            for (int k = 0; k < W; k++) c += popc64(row[k] & U[k]);
            long long sc = (long long)c * 4 + (cur.deg[x] < d_ ? 2 : 0) + rndint(2);
            if (sc > bs) { bs = sc; bx = x; }
        }
        if (bx < 0) break;
        chosen[nc++] = bx;
        const uint64_t *row = B + (size_t)bx * W;
        for (int k = 0; k < W; k++) U[k] &= ~row[k];
    }
    int v = n;
    cur.n = n + 1;
    cur.side[v] = t;
    cur.deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int x = chosen[i];
        if (cur.deg[x] >= d_) {
            int y = cur.adj[x][rndint(cur.deg[x])];
            remove_edge(x, y);
        }
        add_edge(x, v);
    }
}

static void output_state(const State *s) {
    long m = 0;
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++) if (u < s->adj[u][i]) m++;
    printf("%d %ld\n", s->n, m);
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++)
            if (u < s->adj[u][i]) printf("%d %d\n", u, s->adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rng_s ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rng_s == 0) rng_s = 1;
    double avail = tl * 0.92 - 0.25;
    if (avail < 0.05) avail = 0.05;
    deadline_s = now_s() + avail;
    if (d_ < 1 || d_ > MAXDEG || D_ < 2 || 2 * d_ > MAXN - 8) {
        printf("0 0\n");
        return 0;
    }
    if (!read_input()) make_kdd();
    if (cost_now() != 0) anneal(20000, 1.0, 0.1);
    if (cost_now() != 0) {
        printf("0 0\n");
        return 0;
    }
    best = cur;

    int budget = 800;
    while (now_s() < deadline_s && cur.n + 1 < MAXN) {
        snap = cur;
        add_vertex();
        if (anneal(budget, 1.5, 0.1)) {
            fill();
            walk(20);
            fill();
            if (cur.n > best.n) best = cur;
            budget = budget * 7 / 10;
            if (budget < 300) budget = 300;
        } else {
            cur = snap;
            budget = budget * 13 / 10;
            if (budget > 8000) budget = 8000;
            walk(60);
            fill();
        }
    }
    output_state(&best);
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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
# Twin duplication.
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
# Python large-neighbourhood search (kill, repair, regrow), used briefly.
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


def _local_kill(n, adj, k, rng):
    """Pick k vertices forming a connected cluster (BFS-like from a random seed vertex)."""
    v = rng.randrange(n)
    kill = {v}
    frontier = [v]
    while len(kill) < k and frontier:
        x = frontier.pop(rng.randrange(len(frontier)))
        nb = list(adj[x])
        rng.shuffle(nb)
        for u in nb:
            if len(kill) >= k:
                break
            if u not in kill:
                kill.add(u)
                frontier.append(u)
    while len(kill) < k:
        kill.add(rng.randrange(n))
    return kill


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        if rng.random() < 0.6:
            full_adj = _to_sets(cur_n, cur_e)
            kill = _local_kill(cur_n, full_adj, k, rng)
        else:
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
# Entry point.
#
# Stage 1 (Python): structured base (generalized quadrangle for D >= 4,
# projective plane for D = 3), cover growth, short twin trials and a brief LNS.
# Stage 2 (C): vertex insertion by greedy cover of radius D-1 balls, followed by
# simulated annealing over degree-preserving switches and other local moves,
# with an adaptive budget and plateau walks that keep the graph valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.9 * time_limit - 0.3
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.18 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        lns_end = start + 0.3 * time_limit
        if time.monotonic() < lns_end:
            _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and best_n < target and time.monotonic() < end - 1.0:
        budget = end - time.monotonic()
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=budget + 5.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
