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

/* Bipartite diameter-repair annealer with incremental vertex growth.
 * State: bipartite graph with max degree d. Moves:
 *   - add a vertex joined to a greedy cover of the opposite side (radius D-1 balls),
 *   - kill 1-2 random vertices (LNS perturbation),
 *   - fill spare degree across sides,
 *   - anneal with degree-preserving bipartite double-edge switches minimising bad pairs.
 * Every saved best state has zero bad pairs, so the output is always valid.
 */

#define MAXN 4096
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define ITERS 1500

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int side[MAXN];
} State;

static int d, D;
static int n;
static int W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];

static State st_snap, st_best, st_tmp;

static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static uint64_t covbuf[MAXN * MAXW];

static int osn, osm;
static int *oeu, *oev;

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Bitset balls of radius r for all vertices. Returns pointer to result (bufA or bufB). */
static uint64_t *ball_compute(int r) {
    W = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (size_t)(v / 64)] |= 1ULL << (v % 64);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *c = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= c[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long cost(void) {
    uint64_t *b = ball_compute(D);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *row = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(row[w]);
        bad += n - c;
    }
    return bad / 2;
}

static int colour_graph(void) {
    static int stack[MAXN];
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    stack[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void save(State *s) {
    s->n = n;
    for (int i = 0; i < n; i++) {
        s->deg[i] = deg[i];
        s->side[i] = side[i];
        memcpy(s->adj[i], adj[i], sizeof(int) * (size_t)deg[i]);
    }
}

static void load(const State *s) {
    n = s->n;
    for (int i = 0; i < n; i++) {
        deg[i] = s->deg[i];
        side[i] = s->side[i];
        memcpy(adj[i], s->adj[i], sizeof(int) * (size_t)deg[i]);
    }
}

/* New vertex on a random side, joined to a greedy cover of the opposite side.
 * Neighbours already at full degree donate one edge. */
static void add_vertex(void) {
    if (n + 1 >= MAXN) return;
    int c = rndint(2);
    uint64_t *b = ball_compute(D - 1);
    memcpy(covbuf, b, sizeof(uint64_t) * (size_t)n * (size_t)W);
    uint64_t covered[MAXW];
    for (int w = 0; w < W; w++) covered[w] = 0;
    static char used[MAXN];
    memset(used, 0, sizeof used);
    int chosen[MAXD];
    int nch = 0;
    for (int pick = 0; pick < d; pick++) {
        int best = -1;
        double bg = -1.0;
        for (int s = 0; s < n; s++) {
            if (side[s] != 1 - c || used[s]) continue;
            int g = 0;
            const uint64_t *row = covbuf + (size_t)s * W;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(row[w] & ~covered[w]);
            double sc = g + 0.5 * rnd01();
            if (sc > bg) {
                bg = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const uint64_t *row = covbuf + (size_t)best * W;
        for (int w = 0; w < W; w++) covered[w] |= row[w];
    }
    int v = n;
    n++;
    side[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg[s] >= d) {
            int t = adj[s][rndint(deg[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Remove k random vertices (LNS perturbation). */
static void kill_some(int k) {
    if (k <= 0 || k >= n - 2) return;
    static char dead[MAXN];
    static int map[MAXN];
    memset(dead, 0, sizeof dead);
    for (int i = 0; i < k; i++) {
        int x;
        do {
            x = rndint(n);
        } while (dead[x]);
        dead[x] = 1;
    }
    int m = 0;
    for (int v = 0; v < n; v++) map[v] = dead[v] ? -1 : m++;
    State *t = &st_tmp;
    t->n = m;
    for (int v = 0; v < n; v++) {
        if (dead[v]) continue;
        int id = map[v];
        t->side[id] = side[v];
        t->deg[id] = 0;
        for (int k2 = 0; k2 < deg[v]; k2++) {
            int u = adj[v][k2];
            if (!dead[u]) t->adj[id][t->deg[id]++] = map[u];
        }
    }
    load(t);
}

/* Add cross-side edges between deficient vertices (keeps bipartiteness and degrees). */
static void fill(void) {
    int off = rndint(n);
    for (int a = 0; a < n; a++) {
        if (side[a] != 0 || deg[a] >= d) continue;
        for (int ib = 0; ib < n && deg[a] < d; ib++) {
            int b = (ib + off) % n;
            if (side[b] != 1 || deg[b] >= d || has_edge(a, b)) continue;
            add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. Returns final cost. */
static long anneal(int iters, double deadline) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        int a = -1, c = -1;
        for (int t = 0; t < 128 && a < 0; t++) {
            int x = rndint(n);
            if (side[x] == 0 && deg[x] > 0) a = x;
        }
        for (int t = 0; t < 128 && c < 0; t++) {
            int x = rndint(n);
            if (side[x] == 0 && deg[x] > 0 && x != a) c = x;
        }
        if (a < 0 || c < 0) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        if (nc <= cur || (nc == cur + 1 && rnd01() < 0.1)) {
            cur = nc;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void emit_original(void) {
    printf("%d %d\n", osn, osm);
    for (int i = 0; i < osm; i++) printf("%d %d\n", oeu[i], oev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double deadline = now() + budget;

    if (scanf("%d %d", &osn, &osm) != 2 || osn <= 0 || osm < 0) {
        printf("0 0\n");
        return 0;
    }
    oeu = malloc(sizeof(int) * (size_t)(osm + 1));
    oev = malloc(sizeof(int) * (size_t)(osm + 1));
    if (!oeu || !oev) return 1;
    for (int i = 0; i < osm; i++) {
        if (scanf("%d %d", &oeu[i], &oev[i]) != 2) {
            printf("0 0\n");
            return 0;
        }
    }
    if (osn >= MAXN - 64 || d < 1 || d >= MAXD - 1 || D < 2) {
        emit_original();
        return 0;
    }

    for (int v = 0; v < osn; v++) deg[v] = 0;
    int okg = 1;
    for (int i = 0; i < osm && okg; i++) {
        int u = oeu[i], v = oev[i];
        if (u < 0 || u >= osn || v < 0 || v >= osn || u == v) okg = 0;
        else if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) okg = 0;
        else add_edge(u, v);
    }
    n = osn;
    if (!okg || !colour_graph()) {
        emit_original();
        return 0;
    }

    if (cost() != 0) anneal(20000, deadline);
    if (cost() != 0) {
        emit_original();
        return 0;
    }

    save(&st_best);
    int bestn = n;
    int fails = 0;
    while (now() < deadline) {
        save(&st_snap);
        if (n > 12 && rndint(8) == 0) kill_some(1 + rndint(2));
        else add_vertex();
        fill();
        long c = anneal(ITERS, deadline);
        if (c == 0 && n >= bestn - 2) {
            if (n > bestn) {
                bestn = n;
                save(&st_best);
                fails = 0;
            } else {
                fails++;
            }
        } else {
            load(&st_snap);
            fails++;
        }
        if (fails > 400) {
            load(&st_best);
            fails = 0;
        }
    }

    load(&st_best);
    if (cost() != 0) {
        emit_original();
        return 0;
    }
    long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
            for attempt in range(attempts):
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


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Python large-neighbourhood fallback (used only if the C engine cannot run).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# C engine glue.
# ----------------------------------------------------------------------------

def _c_stage(d, D, seed, n, edges, budget):
    """Run the C annealer from (n, edges) for `budget` seconds of CPU time."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n, edges), timeout=budget + 4.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base (short).
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        # Main stage: C annealer with incremental vertex growth from the best graph.
        c_budget = 0.78 * time_limit - (time.monotonic() - start)
        done_c = False
        if c_budget >= 1.0:
            try:
                n2, e2 = _c_stage(d, D, seed, best_n, best_e, c_budget)
                consider(n2, e2)
                done_c = True
            except Exception:
                done_c = False
        # Python fallback if the C stage could not run.
        if not done_c and time.monotonic() < deadline:
            _lns(best_n, best_e, d, D, start + 0.8 * time_limit, rng, consider)
            if time.monotonic() < deadline:
                _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
