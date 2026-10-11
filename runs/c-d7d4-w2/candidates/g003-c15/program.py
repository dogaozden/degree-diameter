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

#define MAXN 2600
#define MAXDEG 48
#define W ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXDEG / 2 + 8)

static int d_, D_;
static int n, nw;
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static int side[MAXN];
static int lst[2][MAXN];
static int lcnt[2];
static uint64_t bufA[MAXN * W], bufB[MAXN * W], ball[MAXN * W];
static uint64_t cov[W];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static int bn, bm;
static int bu[MAXE], bv[MAXE];
static int defA[MAXN], defB[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void set_nw(void) { nw = (n + 63) / 64; }

static void rebuild_lists(void) {
    lcnt[0] = lcnt[1] = 0;
    for (int v = 0; v < n; v++) lst[side[v]][lcnt[side[v]]++] = v;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) if (nb[a][j] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void drop_at(int a, int j) { nb[a][j] = nb[a][--deg[a]]; }

static void remove_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) if (nb[a][j] == b) { drop_at(a, j); break; }
    for (int j = 0; j < deg[b]; j++) if (nb[b][j] == a) { drop_at(b, j); break; }
}

/* out row v = bitmask of vertices within distance r of v (stride W, only nw words used) */
static void compute_balls(int r, uint64_t *out) {
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)nw);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + (size_t)v * W;
            const uint64_t *cv = cur + (size_t)v * W;
            for (int k = 0; k < nw; k++) x[k] = cv[k];
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *cu = cur + (size_t)nb[v][j] * W;
                for (int k = 0; k < nw; k++) x[k] |= cu[k];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    for (int v = 0; v < n; v++)
        memcpy(out + (size_t)v * W, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)nw);
}

/* number of unordered pairs at distance > D_ */
static long cost_bad(void) {
    compute_balls(D_, ball);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *b = ball + (size_t)v * W;
        for (int k = 0; k < nw; k++) c += popc(b[k]);
        bad += n - c;
    }
    return bad / 2;
}

static void fill_random(void) {
    int cA = 0, cB = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d_) {
            if (side[v] == 0) defA[cA++] = v; else defB[cB++] = v;
        }
    }
    long tries = 0, cap = 40L * (cA + cB) + 100;
    while (cA > 0 && cB > 0 && tries < cap) {
        int i = rndint(cA), j = rndint(cB);
        int a = defA[i], b = defB[j];
        tries++;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        if (deg[a] >= d_) defA[i] = defA[--cA];
        if (deg[b] >= d_) defB[j] = defB[--cB];
    }
}

/* Bipartite double-edge switch (degrees preserved), accepted by annealing rule. */
static void anneal_step(long *cur, double T) {
    if (lcnt[0] < 2) return;
    int a = lst[0][rndint(lcnt[0])];
    if (deg[a] == 0) return;
    int b = nb[a][rndint(deg[a])];
    int c = lst[0][rndint(lcnt[0])];
    if (c == a || deg[c] == 0) return;
    int e = nb[c][rndint(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return;
    remove_edge(a, b); remove_edge(c, e);
    add_edge(a, e); add_edge(c, b);
    long nc = cost_bad();
    long delta = nc - *cur;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
        *cur = nc;
    } else {
        remove_edge(a, e); remove_edge(c, b);
        add_edge(a, b); add_edge(c, e);
    }
}

/* Add a vertex on a random side, joined to a greedy cover of the opposite side. */
static void grow_vertex(void) {
    if (n >= MAXN - 2) return;
    int s = rndint(2), t = 1 - s;
    if (lcnt[t] == 0) return;
    int v = n;
    n++;
    set_nw();
    side[v] = s;
    deg[v] = 0;
    rebuild_lists();
    if (D_ >= 2) compute_balls(D_ - 1, ball);
    memset(cov, 0, sizeof cov);
    int chosen[MAXDEG];
    int nch = 0;
    for (int k = 0; k < d_; k++) {
        int best = -1, bestg = 0;
        double bk = -1e18;
        for (int i = 0; i < lcnt[t]; i++) {
            int c = lst[t][i];
            int used = 0;
            for (int q = 0; q < nch; q++) if (chosen[q] == c) { used = 1; break; }
            if (used) continue;
            int g = 0;
            const uint64_t *b = ball + (size_t)c * W;
            for (int w = 0; w < nw; w++) g += popc(b[w] & ~cov[w]);
            double key = g + (deg[c] < d_ ? 0.5 : 0.0) + 0.5 * rnd01();
            if (key > bk) { bk = key; best = c; bestg = g; }
        }
        if (best < 0 || bestg == 0) break;
        chosen[nch++] = best;
        const uint64_t *b = ball + (size_t)best * W;
        for (int w = 0; w < nw; w++) cov[w] |= b[w];
    }
    for (int q = 0; q < nch; q++) {
        int c = chosen[q];
        if (deg[c] >= d_) {
            int x = nb[c][rndint(deg[c])];
            remove_edge(c, x);
        }
        add_edge(v, c);
    }
    fill_random();
}

static void save_best(void) {
    bn = n; bm = 0;
    for (int a = 0; a < n; a++)
        for (int j = 0; j < deg[a]; j++) {
            int b = nb[a][j];
            if (a < b && bm < MAXE) { bu[bm] = a; bv[bm] = b; bm++; }
        }
}

static void restore_best(void) {
    n = bn;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < bm; i++) add_edge(bu[i], bv[i]);
    set_nw();
    rebuild_lists();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t0 = clock();

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (d_ < 1 || d_ > 40 || D_ < 2 || n < 2 || n > MAXN - 200) {
        printf("0 0\n");
        return 0;
    }
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    /* two-colour the graph (BFS); isolated vertices get side 0 */
    static int q[MAXN];
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int h = 0, tl = 0;
        q[tl++] = s;
        while (h < tl) {
            int u = q[h++];
            for (int j = 0; j < deg[u]; j++) {
                int w = nb[u][j];
                if (side[w] < 0) { side[w] = 1 - side[u]; q[tl++] = w; }
            }
        }
    }
    set_nw();
    rebuild_lists();
    save_best();
    long cur = cost_bad();
    double T = 0.4;
    long stall = 0, it = 0;
    const long STALL = 30000;
    while (1) {
        if ((it & 127) == 0 && elapsed() > budget) break;
        it++;
        if (cur == 0) {
            save_best();
            if (n >= MAXN - 2) break;
            grow_vertex();
            cur = cost_bad();
            stall = 0;
            continue;
        }
        anneal_step(&cur, T);
        if (it % 200 == 0) {
            fill_random();
            cur = cost_bad();
        }
        if (++stall > STALL) {
            restore_best();
            T = 0.2 + 0.7 * rnd01();
            grow_vertex();
            cur = cost_bad();
            stall = 0;
        }
    }
    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
'''


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
# Python helpers (construction and fallback search).
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
# C engine driver.
# ----------------------------------------------------------------------------

def _run_engine(d, D, seed, budget, graph):
    """Run the C annealing engine from `graph` for about `budget` seconds. Returns (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=graph, timeout=budget + 10.0)
    return lib.parse_graph_text(text)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit
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
            grow_end = t_start + 0.08 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pipelines for diversity.
    if D >= 2:
        trial_end = t_start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main stage: C annealing engine started from the best valid graph so far.
    if D >= 2:
        c_budget = end - time.monotonic() - 1.5  # leave room for compilation
        if c_budget > 2.0:
            try:
                n, e = _run_engine(d, D, seed, c_budget, (best_n, best_e))
                consider(n, e)
            except Exception:
                pass

    # Fallback if the C stage was unavailable: keep trying Python pipelines.
    if D >= 2:
        while time.monotonic() < end:
            n, e = _trial(best_n, best_e, d, D, rng, end)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
