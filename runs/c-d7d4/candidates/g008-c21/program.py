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

#define MAXN 2048
#define MAXD 40
#define NWMAX 32
#define ITERS 300

typedef struct {
    int n;
    int dg[MAXN];
    int ad[MAXN][MAXD];
    int cl[MAXN];
} State;

static int N = 0, DEG = 3, DIAM = 2, NW = 1;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t ballA[MAXN][NWMAX], ballB[MAXN][NWMAX], ballR[MAXN][NWMAX];
static uint64_t rs = 88172645463325252ULL;
static double tlimit = 0.0;
static int ma, mb, mc, me;
static State st_cur, st_best;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rm_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; return; }
}
static void add_arc(int a, int b) { adj[a][deg[a]++] = b; }
static void add_edge(int a, int b) { add_arc(a, b); add_arc(b, a); }
static void rm_edge(int a, int b) { rm_arc(a, b); rm_arc(b, a); }

/* out[v] = set of vertices within distance r of v (bitmask). */
static void compute_balls(int r, uint64_t out[][NWMAX]) {
    NW = (N + 63) >> 6;
    if (NW < 1) NW = 1;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < NW; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < r; t++) {
        for (int v = 0; v < N; v++)
            for (int w = 0; w < NW; w++) ballR[v][w] = out[v][w];
        for (int v = 0; v < N; v++)
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < NW; w++) out[v][w] |= ballR[u][w];
            }
    }
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static long full_cost(void) {
    compute_balls(DIAM, ballA);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < NW; w++) c += popc(ballA[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int pick_side(int s) {
    for (int t = 0; t < 64; t++) {
        int v = rndi(N);
        if (col[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switch: a-b, c-e -> a-e, c-b. */
static int propose_switch(void) {
    int a = pick_side(0);
    if (a < 0) return 0;
    int c = pick_side(0);
    if (c < 0 || c == a) return 0;
    int b = adj[a][rndi(deg[a])];
    int e = adj[c][rndi(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    rm_edge(a, b); rm_edge(c, e);
    add_edge(a, e); add_edge(c, b);
    ma = a; mb = b; mc = c; me = e;
    return 1;
}

static void undo_switch(void) {
    rm_edge(ma, me); rm_edge(mc, mb);
    add_edge(ma, mb); add_edge(mc, me);
}

static long anneal(long cur) {
    for (int it = 0; it < ITERS && cur > 0; it++) {
        if ((it & 15) == 0 && now() > tlimit) break;
        if (!propose_switch()) continue;
        long nc = full_cost();
        if (nc <= cur || (nc == cur + 1 && rnd01() < 0.05)) cur = nc;
        else undo_switch();
    }
    return cur;
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill_deficient(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    if (nr == 0) return;
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        int off = rndi(nr);
        for (int jj = 0; jj < nr && deg[a] < DEG; jj++) {
            int b = R[(jj + off) % nr];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Append a vertex on side (1-side), joined greedily to a cover of side's vertices. */
static void add_vertex(int side) {
    static uint64_t cov[NWMAX];
    static int chosen[MAXD];
    int nc = 0;
    compute_balls(DIAM - 1, ballB);
    for (int w = 0; w < NW; w++) cov[w] = 0;
    for (int step = 0; step < DEG; step++) {
        int best = -1;
        double bestsc = -1.0;
        for (int s = 0; s < N; s++) {
            if (col[s] != side) continue;
            int used = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < NW; w++) g += popc(ballB[s][w] & ~cov[w]);
            double sc = g + 0.5 * rnd01();
            if (sc > bestsc) { bestsc = sc; best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < NW; w++) cov[w] |= ballB[best][w];
    }
    int v = N;
    N++;
    deg[v] = 0;
    col[v] = 1 - side;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (deg[s] >= DEG) {
            int t = adj[s][rndi(deg[s])];
            rm_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Delete vertex x; the last vertex takes its label. */
static void remove_vertex(int x) {
    for (int k = 0; k < deg[x]; k++) rm_arc(adj[x][k], x);
    deg[x] = 0;
    int y = N - 1;
    if (y != x) {
        for (int k = 0; k < deg[y]; k++) {
            int u = adj[y][k];
            for (int j = 0; j < deg[u]; j++)
                if (adj[u][j] == y) { adj[u][j] = x; break; }
        }
        memcpy(adj[x], adj[y], sizeof(adj[x]));
        deg[x] = deg[y];
        col[x] = col[y];
    }
    deg[y] = 0;
    N = y;
}

static void save_state(State *s) {
    s->n = N;
    memcpy(s->dg, deg, sizeof(deg));
    memcpy(s->ad, adj, sizeof(adj));
    memcpy(s->cl, col, sizeof(col));
}

static void load_state(const State *s) {
    N = s->n;
    memcpy(deg, s->dg, sizeof(deg));
    memcpy(adj, s->ad, sizeof(adj));
    memcpy(col, s->cl, sizeof(col));
}

static void print_state(const State *s) {
    int cnt = 0;
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->dg[v]; k++) if (v < s->ad[v][k]) cnt++;
    printf("%d %d\n", s->n, cnt);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->dg[v]; k++)
            if (v < s->ad[v][k]) printf("%d %d\n", v, s->ad[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tlimit = now() + atof(argv[4]);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > MAXN - 400 || m < 0 ||
        DEG < 1 || DEG > MAXD || DIAM < 2) {
        printf("1 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("1 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
            deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) {
            printf("1 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int u = q[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (col[v] < 0) { col[v] = 1 - col[u]; q[qt++] = v; }
            }
        }
    }
    for (int u = 0; u < N; u++)
        for (int k = 0; k < deg[u]; k++)
            if (col[adj[u][k]] == col[u]) { printf("1 0\n"); return 0; }

    save_state(&st_best);
    if (full_cost() == 0) {
        save_state(&st_cur);
        while (now() < tlimit) {
            if (N < MAXN - 2 && (N < 8 || rndi(10) < 7)) {
                add_vertex(rndi(2));
            } else if (N > 8) {
                remove_vertex(rndi(N));
            }
            fill_deficient();
            long c = full_cost();
            c = anneal(c);
            if (c == 0) {
                save_state(&st_cur);
                if (N > st_best.n) {
                    save_state(&st_best);
                } else if (st_cur.n < st_best.n - 3) {
                    memcpy(&st_cur, &st_best, sizeof(State));
                    load_state(&st_cur);
                }
            } else {
                load_state(&st_cur);
            }
        }
    }
    print_state(&st_best);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for cover growth and saturation.
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 steps."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
# Build: structured base, Python twin trials, then the C repair/regrow engine.
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
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    moore = lib.moore_bound(d, D)

    # Randomized twin-duplication pipelines from the best base so far.
    if D >= 2 and best_n < moore:
        trial_end = start + 0.25 * time_limit
        base_n, base_e = best_n, list(best_e)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C engine: degree-preserving annealing repair, add/remove vertex moves, anchored to best.
    if D >= 2 and best_n < moore:
        end = start + 0.8 * time_limit
        budget = end - time.monotonic() - 1.0  # margin for compilation
        if budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
