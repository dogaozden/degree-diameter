import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine.
#
# Works on a valid bipartite graph with max degree d and diameter <= D.
# Moves (all kept bipartite and degree-bounded):
#   * kill k random vertices (k = 0..2), then add k+1 new vertices, each joined
#     to d opposite-side vertices (a deficient one first; a full one gives up
#     a random edge);
#   * fill spare degree with cross-side edges;
#   * anneal with bipartite double-edge switches (degrees preserved) that
#     minimise the number of pairs at distance > D (bitset balls).
# A state is accepted when the anneal reaches zero bad pairs and the vertex
# count has not dropped by more than one. The walk is anchored to the best
# valid graph. Output is the best valid graph found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXD 40
#define MAXW ((MAXN + 63) / 64)

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int nb[MAXN][MAXD];
} State;

static int N = 0, Dg = 0, DIAM = 2;
static int nb[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static State SA, SB;
static uint64_t rs = 88172645463325252ULL;
static int cand_buf[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int is_adj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}
static void repl(int a, int old, int nw) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == old) { nb[a][i] = nw; return; }
}
static void del_from(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
}
static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}
static void del_edge(int a, int b) { del_from(a, b); del_from(b, a); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long cost_pairs(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

static void save_state(State *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = deg[v];
        s->col[v] = col[v];
        memcpy(s->nb[v], nb[v], sizeof(int) * (size_t)deg[v]);
    }
}
static void load_state(const State *s) {
    N = s->n;
    for (int v = 0; v < N; v++) {
        deg[v] = s->deg[v];
        col[v] = s->col[v];
        memcpy(nb[v], s->nb[v], sizeof(int) * (size_t)deg[v]);
    }
}

/* Remove vertex x; the last vertex takes its label. */
static void kill_vertex(int x) {
    for (int i = 0; i < deg[x]; i++) del_from(nb[x][i], x);
    deg[x] = 0;
    int L = N - 1;
    if (x != L) {
        for (int i = 0; i < deg[L]; i++) repl(nb[L][i], L, x);
        memcpy(nb[x], nb[L], sizeof(int) * (size_t)deg[L]);
        deg[x] = deg[L];
        col[x] = col[L];
    }
    N--;
}

/* Append a vertex joined to up to Dg vertices on the opposite side. */
static void add_vertex(void) {
    int s = rint_(2);
    int v = N++;
    col[v] = 1 - s;
    deg[v] = 0;
    int nc = 0;
    for (int u = 0; u < v; u++) if (col[u] == s) cand_buf[nc++] = u;
    for (int i = nc - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = cand_buf[i];
        cand_buf[i] = cand_buf[j];
        cand_buf[j] = t;
    }
    for (int i = 0; i < nc && deg[v] < Dg; i++) {
        int u = cand_buf[i];
        if (deg[u] < Dg) add_edge(u, v);
    }
    for (int i = 0; i < nc && deg[v] < Dg; i++) {
        int u = cand_buf[i];
        if (deg[u] < Dg || is_adj(u, v)) continue;
        int w = nb[u][rint_(deg[u])];
        del_edge(u, w);
        add_edge(u, v);
    }
}

/* Random cross-side edges between vertices with spare degree. */
static void fill_edges(int tries) {
    for (int t = 0; t < tries; t++) {
        int a = rint_(N), b = rint_(N);
        if (col[a] == col[b]) continue;
        if (col[a] == 1) { int x = a; a = b; b = x; }
        if (deg[a] >= Dg || deg[b] >= Dg || is_adj(a, b)) continue;
        add_edge(a, b);
    }
}

/* Bipartite double-edge switches minimising bad pairs. Returns 1 if cost reached 0. */
static int anneal(int iters, long long *out) {
    long long cur = cost_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        int a = rint_(N);
        if (col[a] != 0 || deg[a] == 0) continue;
        int c = rint_(N);
        if (col[c] != 0 || deg[c] == 0 || c == a) continue;
        int b = nb[a][rint_(deg[a])];
        int e = nb[c][rint_(deg[c])];
        if (b == e || is_adj(a, e) || is_adj(c, b)) continue;
        /* a-b, c-e  ->  a-e, c-b */
        repl(a, b, e);
        repl(c, e, b);
        repl(b, a, c);
        repl(e, c, a);
        long long nw = cost_pairs();
        if (nw <= cur || (nw == cur + 1 && rdbl() < 0.03)) {
            cur = nw;
        } else {
            repl(a, e, b);
            repl(c, b, e);
            repl(b, c, a);
            repl(e, a, c);
        }
    }
    *out = cur;
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    if (DIAM < 1) DIAM = 1;
    unsigned long seed = strtoul(argv[3], NULL, 10);
    long budget = atol(argv[4]);
    time_t t0 = time(NULL);
    time_t deadline = t0 + (time_t)budget;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    Dg = d;
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1 || n > MAXN || d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= Dg || deg[v] >= Dg || is_adj(u, v)) continue;
        add_edge(u, v);
    }

    /* Bipartition by BFS; a non-bipartite input cannot be used. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < N && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && ok) {
            int x = q[qh++];
            for (int i = 0; i < deg[x]; i++) {
                int y = nb[x][i];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    q[qt++] = y;
                } else if (col[y] == col[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    int bestN = -1;
    long long c0 = cost_pairs();
    if (c0 == 0) {
        save_state(&SB);
        bestN = N;
    }
    int curN = N;

    while (time(NULL) < deadline) {
        save_state(&SA);
        int k = rint_(3);
        for (int i = 0; i < k && N > 1; i++) kill_vertex(rint_(N));
        for (int i = 0; i < k + 1 && N < MAXN - 1; i++) add_vertex();
        fill_edges(4 * N);
        long long c = 0;
        anneal(800, &c);
        if (c == 0) {
            if (N > bestN) {
                bestN = N;
                save_state(&SB);
            }
            if (N >= curN - 1) {
                curN = N;
            } else {
                load_state(&SA);
            }
        } else {
            load_state(&SA);
        }
        if (curN < bestN - 3) {
            load_state(&SB);
            curN = N;
        }
    }

    if (bestN < 0) { printf("0 0\n"); return 0; }
    load_state(&SB);
    int me = 0;
    for (int v = 0; v < N; v++) me += deg[v];
    me /= 2;
    printf("%d %d\n", N, me);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (nb[u][i] > u) printf("%d %d\n", u, nb[u][i]);
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
# Python helpers for cheap cover growth and twin duplication.
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
    """Greedily join deficient opposite-side vertices in random order. Keeps diameter valid."""
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
            nb_set = adj[v]
            if not nb_set or len(nb_set) > d:
                continue
            if any(len(adj[u]) >= d for u in nb_set):
                continue
            w = len(adj)
            adj.append(set(nb_set))
            for u in nb_set:
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_total = start + 0.92 * time_limit
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.06 * time_limit, rng)
            consider(n1, e1)

    # Stop early if the graph already meets the Moore bound (calibration cases).
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Short randomized twin-duplication pass from the current best.
    if D >= 2:
        base_n, base_e = best_n, list(best_e)
        trial_end = start + 0.10 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main search: C engine (kill / regrow / bipartite switch annealing).
    if D >= 2:
        budget = int(end_total - time.monotonic()) - 4
        if budget >= 3:
            try:
                txt = lib.run_c(C_SOURCE, [d, D, int(seed) & 0xFFFFFFFF, budget],
                                stdin_graph=(best_n, best_e), timeout=budget + 20)
                n, e = lib.parse_graph_text(txt)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
