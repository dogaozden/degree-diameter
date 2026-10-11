import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost simulated annealing with kill / add / repair moves.
#
# The state is a valid bipartite graph (cost = number of pairs at distance > D).
# Moves:
#   * bipartite double-edge switches (degrees and sides preserved), accepted by
#     the Metropolis rule on the bad-pair count;
#   * kill k random vertices, add k+1 vertices with greedy cover neighbourhoods
#     (a cover of the side opposite the new vertex), fill spare degree, anneal.
# Any state with cost 0 and size >= the anchor size becomes the new anchor, so
# the walk climbs in size and drifts sideways across plateaus.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXD 64
#define MAXW 16
#define ITERS 2500

typedef uint64_t u64;

static int DEG_MAX, DIAM;
static int N;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} Snap;

static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd() % (u64)m); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static u64 BA[MAXN][MAXW], BB[MAXN][MAXW], BALL[MAXN][MAXW];

/* out[v] = bitset of vertices within distance r of v. */
static void balls(int r, u64 out[][MAXW]) {
    int W = (N + 63) / 64;
    u64 (*cur)[MAXW] = BA;
    u64 (*nxt)[MAXW] = BB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) out[v][w] = cur[v][w];
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long cost(void) {
    int W = (N + 63) / 64;
    balls(DIAM, BALL);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(BALL[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

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

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Remove vertex x, relabelling the last vertex to x. */
static void kill_vertex(int x) {
    while (deg[x] > 0) del_edge(x, adj[x][0]);
    int last = N - 1;
    if (x != last) {
        for (int k = 0; k < deg[last]; k++) {
            int y = adj[last][k];
            for (int j = 0; j < deg[y]; j++) {
                if (adj[y][j] == last) {
                    adj[y][j] = x;
                    break;
                }
            }
        }
        deg[x] = deg[last];
        memcpy(adj[x], adj[last], sizeof(int) * MAXD);
        col[x] = col[last];
    }
    deg[last] = 0;
    N--;
}

/* Add a vertex on the side opposite to s, joined to a greedy cover of side s. */
static int add_vertex(int s) {
    int v = N++;
    col[v] = 1 - s;
    deg[v] = 0;
    balls(DIAM - 1, BALL);
    int W = (N + 63) / 64;
    u64 cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    cov[v >> 6] |= 1ULL << (v & 63);
    int chosen[MAXD];
    int nch = 0;
    for (int pick = 0; pick < DEG_MAX && nch < DEG_MAX; pick++) {
        int best = -1, bestg = 0;
        for (int x = 0; x < N - 1; x++) {
            if (col[x] != s) continue;
            int used = 0;
            for (int i = 0; i < nch; i++)
                if (chosen[i] == x) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(BALL[x][w] & ~cov[w]);
            if (g > bestg || (g == bestg && g > 0 && rndint(2))) {
                bestg = g;
                best = x;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= BALL[best][w];
    }
    for (int i = 0; i < nch; i++) {
        int x = chosen[i];
        if (deg[x] >= DEG_MAX) {
            int t = adj[x][rndint(deg[x])];
            del_edge(x, t);
        }
        add_edge(x, v);
    }
    return v;
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Join deficient opposite-side vertices in random order. */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG_MAX) {
            if (col[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1; j++) {
            if (deg[a] >= DEG_MAX) break;
            int b = L1[j];
            if (deg[b] < DEG_MAX && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int S0[MAXN];

/* Bipartite double-edge switches minimising the bad-pair count. Returns 1 if cost reaches 0. */
static int anneal(int iters, double T0, double T1) {
    int ns = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0) S0[ns++] = v;
    if (ns < 2) return 0;
    long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int a = S0[rndint(ns)];
        int c = S0[rndint(ns)];
        if (a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost();
        if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void save_snap(Snap *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->col, col, sizeof col);
}

static void load_snap(const Snap *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
    memcpy(col, s->col, sizeof col);
}

static void print_state(void) {
    int m = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) m++;
    printf("%d %d\n", N, m);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
}

static Snap base_s, best_s;

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DEG_MAX = d;
    DIAM = D;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d < 2 || d > MAXD || D < 2 || n0 < 2 || n0 > MAXN - 64) {
        printf("0 0\n");
        return 0;
    }
    N = n0;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= DEG_MAX || deg[v] >= DEG_MAX || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    /* 2-colour the start graph; reject it if it is not bipartite. */
    for (int v = 0; v < N; v++) col[v] = -1;
    static int stk[MAXN];
    int bip = 1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    bip = 0;
                }
            }
        }
    }
    if (!bip || cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    save_snap(&best_s);
    save_snap(&base_s);
    int baseN = N;
    int bestN = N;

    while ((double)(clock() - t0) / CLOCKS_PER_SEC < budget) {
        load_snap(&base_s);
        int mode = rndint(3);
        int kills = (mode == 0) ? 0 : (mode == 1 ? 1 : 2);
        if (N <= kills + 3) kills = 0;
        if (N + kills + 2 >= MAXN) break;
        for (int k = 0; k < kills; k++) kill_vertex(rndint(N));
        for (int k = 0; k < kills + 1; k++) add_vertex(rndint(2));
        fill();
        if (anneal(ITERS, 0.6, 0.05)) {
            if (N >= baseN) {
                save_snap(&base_s);
                baseN = N;
                if (N > bestN) {
                    bestN = N;
                    save_snap(&best_s);
                }
            }
        }
    }

    load_snap(&best_s);
    print_state();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured constructions.
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
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. Twins
# keep distances to all other vertices, so duplicating never breaks the
# diameter bound (for D >= 2), keeps bipartiteness, and needs only spare degree
# on the neighbours of v.
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
# Build: structured base, Python twin pipelines, then the C annealing engine.
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
            grow_end = start + 0.2 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing engine from the best valid graph found so far.
    ceiling = lib.moore_bound(d, D)
    if D >= 2 and 2 <= d <= 60 and best_n < ceiling and best_n < 900:
        elapsed = time.monotonic() - start
        c_budget = 0.8 * time_limit - elapsed - 0.5
        if c_budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=c_budget + 8.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
