import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-based annealing over bipartite graphs with max degree d and
# diameter <= D. The state always satisfies degree <= d, bipartiteness (fixed
# 2-colouring), and no duplicate edges. The cost is the number of unordered
# vertex pairs at distance > D. Vertices are added whenever the current state
# is valid, and the engine searches for a valid graph with one more vertex.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 64
#define MAXW 32

typedef struct {
    int n;
    int side[MAXN];
    int deg[MAXN];
    int adj[MAXN * MAXDEG];
} State;

static int d_, D_;
static int n_;
static int side_[MAXN];
static int deg_[MAXN];
static int adj_[MAXN * MAXDEG];
static State undo_, best_;
static int best_n_ = -1;
static int cur_cost_ = 0;
static uint64_t bufA_[MAXN * MAXW];
static uint64_t bufB_[MAXN * MAXW];
static uint64_t rng_s_ = 88172645463325252ULL;

static uint64_t rnd(void) {
    rng_s_ ^= rng_s_ << 13;
    rng_s_ ^= rng_s_ >> 7;
    rng_s_ ^= rng_s_ << 17;
    return rng_s_;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (adj_[a * d_ + i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj_[a * d_ + deg_[a]++] = b;
    adj_[b * d_ + deg_[b]++] = a;
}

static void del_from(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a * d_ + i] == b) {
            adj_[a * d_ + i] = adj_[a * d_ + deg_[a] - 1];
            deg_[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

static int eval_cost(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    uint64_t *cur = bufA_;
    uint64_t *nxt = bufB_;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg_[v]; i++) {
                const uint64_t *c2 = cur + (size_t)adj_[v * d_ + i] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const uint64_t *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += popc(c[w]);
        miss += n - cnt;
    }
    return (int)(miss / 2);
}

static void save_state(State *s) {
    s->n = n_;
    memcpy(s->side, side_, sizeof(int) * (size_t)n_);
    memcpy(s->deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(s->adj, adj_, sizeof(int) * (size_t)n_ * (size_t)d_);
}

static void restore_state(const State *s) {
    n_ = s->n;
    memcpy(side_, s->side, sizeof(int) * (size_t)n_);
    memcpy(deg_, s->deg, sizeof(int) * (size_t)n_);
    memcpy(adj_, s->adj, sizeof(int) * (size_t)n_ * (size_t)d_);
}

/* Add a new vertex on a random side, attached to d_ opposite vertices. */
static void add_vertex(void) {
    int x = n_++;
    deg_[x] = 0;
    int s = rndi(2);
    side_[x] = s;
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < x; v++)
        if (side_[v] != s && deg_[v] < d_) cand[nc++] = v;
    for (int i = nc - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    int k = 0;
    for (int i = 0; i < nc && k < d_; i++) {
        add_edge(x, cand[i]);
        k++;
    }
    int tries = 0;
    while (k < d_ && tries < 400) {
        tries++;
        int y = rndi(x);
        if (side_[y] == s || has_edge(x, y)) continue;
        if (deg_[y] < d_) {
            add_edge(x, y);
        } else {
            int z = adj_[y * d_ + rndi(deg_[y])];
            remove_edge(y, z);
            add_edge(x, y);
        }
        k++;
    }
}

/* Add an edge between two spare opposite-side vertices. Returns 1 if applied. */
static int try_fill(void) {
    for (int t = 0; t < 50; t++) {
        int a = rndi(n_), b = rndi(n_);
        if (side_[a] == side_[b] || deg_[a] >= d_ || deg_[b] >= d_ || has_edge(a, b)) continue;
        add_edge(a, b);
        return 1;
    }
    return 0;
}

/* Degree-preserving 2-switch. Returns 1 if applied. */
static int move_switch(void) {
    int x = rndi(n_);
    if (!deg_[x]) return 0;
    int y = adj_[x * d_ + rndi(deg_[x])];
    int x2 = rndi(n_);
    if (!deg_[x2]) return 0;
    int y2 = adj_[x2 * d_ + rndi(deg_[x2])];
    int p = x, q = y, p2 = x2, q2 = y2;
    if (side_[p] == 1) { int t = p; p = q; q = t; }
    if (side_[p2] == 1) { int t = p2; p2 = q2; q2 = t; }
    if (p == p2 || q == q2) return 0;
    if (has_edge(p, q2) || has_edge(p2, q)) return 0;
    remove_edge(p, q);
    remove_edge(p2, q2);
    add_edge(p, q2);
    add_edge(p2, q);
    return 1;
}

/* Move one endpoint of an edge to another spare vertex. Returns 1 if applied. */
static int move_rewire(void) {
    int x = rndi(n_);
    if (!deg_[x]) return 0;
    int y = adj_[x * d_ + rndi(deg_[x])];
    for (int t = 0; t < 30; t++) {
        int z = rndi(n_);
        if (side_[z] != side_[y] || z == y || deg_[z] >= d_ || has_edge(x, z)) continue;
        remove_edge(x, y);
        add_edge(x, z);
        return 1;
    }
    return 0;
}

/* Attach x to y, displacing one random edge of y if y is full. Returns 1 if applied. */
static int move_steal(void) {
    int x = rndi(n_);
    if (deg_[x] >= d_) return 0;
    int y = rndi(n_);
    if (side_[y] == side_[x] || has_edge(x, y)) return 0;
    if (deg_[y] < d_) {
        add_edge(x, y);
        return 1;
    }
    int z = adj_[y * d_ + rndi(deg_[y])];
    remove_edge(y, z);
    add_edge(x, y);
    return 1;
}

static void anneal_step(double T) {
    save_state(&undo_);
    double r = rndd();
    int ok;
    if (r < 0.15) ok = try_fill();
    else if (r < 0.55) ok = move_switch();
    else if (r < 0.85) ok = move_rewire();
    else ok = move_steal();
    if (!ok) return;
    int c2 = eval_cost();
    int delta = c2 - cur_cost_;
    if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
        cur_cost_ = c2;
    } else {
        restore_state(&undo_);
    }
}

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget [moore]\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int moore = argc > 5 ? atoi(argv[5]) : 0;
    rng_s_ ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rng_s_ == 0) rng_s_ = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (d_ < 1 || d_ > MAXDEG || D_ < 1 || n < 0 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    memset(deg_, 0, sizeof(deg_));
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok || n == 0) {
        printf("0 0\n");
        return 0;
    }

    /* 2-colour the input; reject if not bipartite. */
    for (int v = 0; v < n; v++) side_[v] = -1;
    int *queue = (int *)malloc(sizeof(int) * (size_t)(n + 1));
    for (int s = 0; s < n && ok; s++) {
        if (side_[s] >= 0) continue;
        side_[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail && ok) {
            int u = queue[head++];
            for (int i = 0; i < deg_[u]; i++) {
                int w = adj_[u * d_ + i];
                if (side_[w] < 0) {
                    side_[w] = 1 - side_[u];
                    queue[tail++] = w;
                } else if (side_[w] == side_[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(queue);
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    cur_cost_ = eval_cost();
    for (int i = 0; i < 3000; i++) try_fill();
    cur_cost_ = eval_cost();
    if (cur_cost_ == 0) {
        save_state(&best_);
        best_n_ = n_;
    }

    const int STALL = 4000;
    int stall = 0;
    while (elapsed(t0) < budget) {
        if (moore > 0 && best_n_ >= moore) break;
        if (cur_cost_ == 0) {
            if (n_ > best_n_) {
                save_state(&best_);
                best_n_ = n_;
            }
            if (n_ >= MAXN - 1) break;
            add_vertex();
            cur_cost_ = eval_cost();
            stall = 0;
            continue;
        }
        double T = 0.05 + 1.0 * (1.0 - (double)stall / (double)STALL);
        anneal_step(T);
        stall++;
        if (stall >= STALL) {
            if (best_n_ >= 0) restore_state(&best_);
            cur_cost_ = eval_cost();
            stall = 0;
        }
    }

    if (best_n_ < 0) {
        printf("0 0\n");
        return 0;
    }
    long long total = 0;
    for (int u = 0; u < best_.n; u++) total += best_.deg[u];
    total /= 2;
    printf("%d %lld\n", best_.n, total);
    for (int u = 0; u < best_.n; u++) {
        for (int i = 0; i < best_.deg[u]; i++) {
            int v = best_.adj[u * d_ + i];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (diameter 3 arc-extended projective plane graphs, and W(q) for D = 4).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s entries of S (repeats counted)."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _multi_side(m, s, nbr, rng, deadline):
    """Iterated greedy over multisets so every target is hit <= s times."""
    order = list(range(m))

    def fill(S, load):
        rng.shuffle(order)
        for x in order:
            nb = nbr[x]
            while all(load[t] < s for t in nb):
                S.append(x)
                for t in nb:
                    load[t] += 1
        return S

    cur = fill([], [0] * m)
    best = list(cur)
    while time.monotonic() < deadline:
        S = list(cur)
        load = [0] * m
        for x in S:
            for t in nbr[x]:
                load[t] += 1
        for _ in range(min(rng.randint(1, 3), len(S))):
            i = rng.randrange(len(S))
            x = S.pop(i)
            for t in nbr[x]:
                load[t] -= 1
        S = fill(S, load)
        if len(S) >= len(cur):
            cur = S
            if len(cur) > len(best):
                best = list(cur)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA entry and one new B-vertex per SB entry."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates from PG(2, q) extensions, for the largest few prime powers q."""
    out = []
    qs = sorted((q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)), reverse=True)[:3]
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        per_side = (deadline - now) / (2 * (len(qs) - idx))
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        if s >= 1:
            SA = _multi_side(m, s, point_lines, rng, time.monotonic() + per_side)
            SB = _multi_side(m, s, line_points, rng, time.monotonic() + per_side)
        else:
            SA, SB = [], []
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _largest_valid(cands, d, D):
    """Return the largest candidate (n, edges) that passes lib.is_valid, or None."""
    for n, e in sorted(cands, key=lambda t: -t[0]):
        if lib.is_valid(n, e, d, D):
            return (n, e)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback

    cands = []
    if D >= 3:
        cands += _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
    if D >= 4 and time.monotonic() - t0 < 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)
    got = _largest_valid(cands, d, D) if cands else None
    if got is not None and got[0] > best[0]:
        best = got

    # Bold change: C annealing with vertex insertion, started from the best valid graph.
    elapsed = time.monotonic() - t0
    budget_c = 0.75 * time_limit - elapsed
    if budget_c > 1.0 and d <= 60:
        moore = lib.moore_bound(d, D)
        timeout = max(1.0, 0.85 * time_limit - elapsed)
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget_c:.2f}", moore],
                            stdin_graph=best, timeout=timeout)
            g = lib.parse_graph_text(out)
        except (RuntimeError, ValueError):
            g = None
        if g is not None and g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = g

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
