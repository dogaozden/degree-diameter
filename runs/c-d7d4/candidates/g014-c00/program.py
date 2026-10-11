import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define WMAX 32
#define ITERS 3000

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int color[MAXN];
    int adj[MAXN][MAXD];
} State;

static State cur, best;
static int dd, DD;
static u64 rs;
static double budget_s;
static clock_t t0;
static u64 BA[MAXN * WMAX], BB[MAXN * WMAX];
static int EU[MAXN * MAXD], EV[MAXN * MAXD];

static int time_up(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC >= budget_s;
}

static u64 rnext(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rint_(int m) { return (int)(rnext() % (u64)m); }

static double rdbl(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < cur.deg[a]; i++)
        if (cur.adj[a][i] == b) return 1;
    return 0;
}

static void edge_del1(int a, int b) {
    for (int i = 0; i < cur.deg[a]; i++) {
        if (cur.adj[a][i] == b) {
            cur.adj[a][i] = cur.adj[a][--cur.deg[a]];
            return;
        }
    }
}

static void edge_del(int a, int b) {
    edge_del1(a, b);
    edge_del1(b, a);
}

static void edge_add(int a, int b) {
    cur.adj[a][cur.deg[a]++] = b;
    cur.adj[b][cur.deg[b]++] = a;
}

/* Number of unordered pairs at distance > DD (unreachable pairs count). */
static long long cost_bad(void) {
    int n = cur.n;
    int Wn = (n + 63) >> 6;
    u64 *a = BA, *b = BB;
    memset(a, 0, sizeof(u64) * (size_t)n * Wn);
    for (int v = 0; v < n; v++) a[(size_t)v * Wn + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            u64 *o = b + (size_t)v * Wn;
            const u64 *c = a + (size_t)v * Wn;
            memcpy(o, c, sizeof(u64) * Wn);
            for (int i = 0; i < cur.deg[v]; i++) {
                const u64 *s = a + (size_t)cur.adj[v][i] * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= s[w];
            }
        }
        u64 *t = a;
        a = b;
        b = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *c = a + (size_t)v * Wn;
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += __builtin_popcountll(c[w]);
        bad += n - pc;
    }
    return bad / 2;
}

static int pick_side(int side) {
    for (int t = 0; t < 100000; t++) {
        int v = rint_(cur.n);
        if (cur.color[v] == side && cur.deg[v] > 0) return v;
    }
    return -1;
}

static void shuffle(int *x, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill_up(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < cur.n; v++) {
        if (cur.deg[v] < dd) {
            if (cur.color[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && cur.deg[a] < dd; j++) {
            int b = L1[j];
            if (cur.deg[b] < dd && !has_edge(a, b)) edge_add(a, b);
        }
    }
}

/* Append a vertex on `side`, joined to d vertices of the other side. */
static void add_vertex(int side) {
    static int cand[MAXN];
    int v = cur.n++;
    cur.color[v] = side;
    cur.deg[v] = 0;
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (cur.color[u] == 1 - side) cand[nc++] = u;
    shuffle(cand, nc);
    int chosen = 0;
    for (int i = 0; i < nc && chosen < dd; i++) {
        if (cur.deg[cand[i]] < dd) {
            edge_add(cand[i], v);
            chosen++;
        }
    }
    for (int i = 0; i < nc && chosen < dd; i++) {
        int u = cand[i];
        if (cur.deg[u] < dd || has_edge(u, v)) continue;
        int t = cur.adj[u][rint_(cur.deg[u])];
        edge_del(u, t);
        edge_add(u, v);
        chosen++;
    }
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    for (int i = 0; i < cur.deg[x]; i++) {
        int t = cur.adj[x][i];
        for (int j = 0; j < cur.deg[t]; j++) {
            if (cur.adj[t][j] == x) {
                cur.adj[t][j] = cur.adj[t][--cur.deg[t]];
                break;
            }
        }
    }
    cur.deg[x] = 0;
    int last = cur.n - 1;
    if (x != last) {
        cur.color[x] = cur.color[last];
        cur.deg[x] = cur.deg[last];
        memcpy(cur.adj[x], cur.adj[last], sizeof(int) * cur.deg[last]);
        for (int i = 0; i < cur.deg[x]; i++) {
            int t = cur.adj[x][i];
            for (int j = 0; j < cur.deg[t]; j++) {
                if (cur.adj[t][j] == last) {
                    cur.adj[t][j] = x;
                    break;
                }
            }
        }
    }
    cur.n--;
}

/* Bipartite double-edge switches (degrees and sides preserved) minimising bad pairs.
   Returns 1 if cost reaches 0. */
static int anneal(int iters, double T) {
    long long c = cost_bad();
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && time_up()) break;
        int a = pick_side(0), cc = pick_side(0);
        if (a < 0 || cc < 0 || a == cc) continue;
        int b = cur.adj[a][rint_(cur.deg[a])];
        int e = cur.adj[cc][rint_(cur.deg[cc])];
        if (b == e || has_edge(a, e) || has_edge(cc, b)) continue;
        edge_del(a, b);
        edge_del(cc, e);
        edge_add(a, e);
        edge_add(cc, b);
        long long nc = cost_bad();
        long long delta = nc - c;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            c = nc;
        } else {
            edge_del(a, e);
            edge_del(cc, b);
            edge_add(a, b);
            edge_add(cc, e);
        }
    }
    return c == 0;
}

static void print_graph(const State *s) {
    int m = 0;
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (s->adj[v][i] > v) m++;
    printf("%d %d\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (s->adj[v][i] > v) printf("%d %d\n", v, s->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 88172645463325252ULL;
    budget_s = atof(argv[4]);
    t0 = clock();
    if (dd < 1 || dd >= MAXD || DD < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    memset(&cur, 0, sizeof(cur));
    int ok = 1;
    if (n0 <= 0) {
        cur.n = 2 * dd;
        for (int a = 0; a < dd; a++)
            for (int b = 0; b < dd; b++) {
                cur.color[dd + b] = 1;
                edge_add(a, dd + b);
            }
    } else if (n0 > MAXN - 2 || m0 < 0 || m0 > MAXN * MAXD / 2) {
        ok = 0;
    } else {
        cur.n = n0;
        for (int i = 0; i < m0 && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v ||
                cur.deg[u] >= dd || cur.deg[v] >= dd || has_edge(u, v)) {
                ok = 0;
                break;
            }
            edge_add(u, v);
        }
    }
    if (ok) {
        /* Two-colour the graph; reject non-bipartite input. */
        static int col[MAXN], stk[MAXN];
        for (int v = 0; v < cur.n; v++) col[v] = -1;
        for (int s = 0; s < cur.n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp > 0) {
                int u = stk[--sp];
                for (int i = 0; i < cur.deg[u]; i++) {
                    int w = cur.adj[u][i];
                    if (col[w] == -1) {
                        col[w] = 1 - col[u];
                        stk[sp++] = w;
                    } else if (col[w] == col[u]) {
                        ok = 0;
                    }
                }
            }
        }
        for (int v = 0; v < cur.n; v++) cur.color[v] = col[v] < 0 ? 0 : col[v];
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    best = cur;
    if (cost_bad() != 0) {
        print_graph(&best);
        return 0;
    }

    while (!time_up()) {
        cur = best;
        int target = best.n + 1;
        if (rnext() % 10 < 3) {
            /* plateau move: drop a random vertex, then regrow to the same order */
            remove_vertex(rint_(cur.n));
            target = best.n;
        }
        if (target >= MAXN - 1) break;
        while (cur.n < target) add_vertex(rint_(2));
        fill_up();
        double T = 0.3 + 0.7 * rdbl();
        if (anneal(ITERS, T)) best = cur;
    }

    print_graph(&best);
    return 0;
}
'''


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
# Twin duplication: a non-adjacent twin of v (same neighbourhood) keeps the
# diameter bound for D >= 2, stays on v's side, and needs only spare degree.
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
# Python large-neighbourhood search (kill, repair, regrow), anchored to its best.
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# build: structured base, then Python pipelines, then the C engine
# (add-one-vertex and anneal with bitset bad-pair cost) from the best graph.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    def left(frac):
        """Seconds remaining until start + frac * T."""
        return start + frac * T - time.monotonic()

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

    base_n, base_e = best_n, list(best_e)
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            if best_n >= lib.moore_bound(d, D):
                return best_n, list(best_e)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * T, rng)
            consider(n1, e1)

    if D >= 2 and best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * T
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Python kill-repair-regrow search.
    if D >= 2 and time.monotonic() < start + 0.3 * T:
        _lns(best_n, best_e, d, D, start + 0.3 * T, rng, consider)

    # C engine: add a vertex, anneal the bad-pair cost to zero, keep improvements.
    if D >= 2 and d <= 60 and best_n <= 1500:
        rem = left(0.85)
        if rem > 3.0:
            budget = max(1.0, rem - 1.0)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, left(0.93)))
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
