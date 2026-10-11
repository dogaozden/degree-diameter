import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 3072
#define MAXDEG 64
#define WMAX (MAXN / 64)
#define STALL 20000L
#define TEMP 0.35

static int n, dg, DM;
static int deg[MAXN];
static int adjv[MAXN][MAXDEG];
static int col[MAXN];
static uint64_t bufA[MAXN][WMAX];
static uint64_t bufB[MAXN][WMAX];
static uint64_t tmpb[MAXN][WMAX];
static int W;
static uint64_t rs = 88172645463325252ULL;
static int bestn = 0, bestm = 0, have_best = 0;
static int bestcol[MAXN];
static int bu[MAXN * MAXDEG / 2], bv[MAXN * MAXDEG / 2];
static int ua, ub, uc, ue;
static double tlimit;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* out[v] = bitmask of vertices within distance radius of v (bitset BFS). */
static void compute_balls(int radius, uint64_t out[][WMAX]) {
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = out[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjv[v][k];
                for (int w = 0; w < W; w++) tmpb[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmpb[v][w];
    }
}

/* Number of unordered pairs at distance more than DM (unreachable counts). */
static long cost_full(void) {
    compute_balls(DM, bufA);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc(bufA[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int x, int y) {
    for (int k = 0; k < deg[x]; k++) if (adjv[x][k] == y) return 1;
    return 0;
}

static void add_edge(int x, int y) {
    adjv[x][deg[x]++] = y;
    adjv[y][deg[y]++] = x;
}

static void del_from(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (adjv[x][k] == y) {
            adjv[x][k] = adjv[x][--deg[x]];
            return;
        }
    }
}

static void del_edge(int x, int y) { del_from(x, y); del_from(y, x); }

/* Join deficient opposite-side pairs. Only shortens distances, so cost never rises. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dg) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    if (nr == 0) return;
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        int off = rndi(nr);
        for (int j = 0; j < nr && deg[a] < dg; j++) {
            int b = R[(j + off) % nr];
            if (deg[b] < dg && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add a vertex on the side opposite to s, joined to a greedy cover (radius DM-1) of side s.
   Saturated neighbours give up a random edge. */
static void add_vertex(void) {
    if (n >= MAXN - 1) return;
    int s = rndi(2);
    compute_balls(DM - 1, bufB);
    static char used[MAXN];
    static int chosen[MAXDEG];
    uint64_t covered[WMAX];
    int nc = 0;
    for (int w = 0; w < W; w++) covered[w] = 0;
    for (int x = 0; x < n; x++) used[x] = 0;
    for (int k = 0; k < dg; k++) {
        int best = -1;
        double bs = -1e18;
        for (int x = 0; x < n; x++) {
            if (col[x] != s || used[x]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc(bufB[x][w] & ~covered[w]);
            double sc = g + 0.5 * rndu() - (deg[x] >= dg ? 0.75 : 0.0);
            if (sc > bs) { bs = sc; best = x; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) covered[w] |= bufB[best][w];
    }
    int v = n;
    n++;
    col[v] = 1 - s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int x = chosen[i];
        if (deg[x] >= dg) {
            int t = adjv[x][rndi(deg[x])];
            del_edge(x, t);
        }
        add_edge(x, v);
    }
}

/* Bipartite double-edge switch: a-b, c-e -> a-e, c-b. Degrees and bipartition preserved. */
static int try_switch(void) {
    int s = rndi(2);
    int a = -1, c = -1;
    for (int t = 0; t < 40 && a < 0; t++) {
        int x = rndi(n);
        if (col[x] == s && deg[x] > 0) a = x;
    }
    for (int t = 0; t < 40 && c < 0; t++) {
        int x = rndi(n);
        if (col[x] == s && deg[x] > 0 && x != a) c = x;
    }
    if (a < 0 || c < 0) return 0;
    int b = adjv[a][rndi(deg[a])];
    int e = adjv[c][rndi(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    ua = a; ub = b; uc = c; ue = e;
    return 1;
}

static void undo_switch(void) {
    del_edge(ua, ue);
    del_edge(uc, ub);
    add_edge(ua, ub);
    add_edge(uc, ue);
}

static void snapshot(void) {
    bestn = n;
    bestm = 0;
    for (int v = 0; v < n; v++) {
        bestcol[v] = col[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adjv[v][k];
            if (v < u && bestm < MAXN * MAXDEG / 2) {
                bu[bestm] = v;
                bv[bestm] = u;
                bestm++;
            }
        }
    }
    have_best = 1;
}

static void restore(void) {
    n = bestn;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = bestcol[v];
    }
    for (int i = 0; i < bestm; i++) add_edge(bu[i], bv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlimit = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    dg = d;
    DM = D;
    if (d < 1 || d > MAXDEG || D < 2 || n0 < 1 || n0 > MAXN - 600 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n = n0;
    for (int v = 0; v < n; v++) { deg[v] = 0; col[v] = -1; }
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || u >= n || v < 0 || v >= n || u == v || deg[u] >= dg || deg[v] >= dg || has_edge(u, v)) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    static int q[MAXN];
    for (int s0 = 0; s0 < n && ok; s0++) {
        if (col[s0] != -1) continue;
        col[s0] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s0;
        while (qh < qt) {
            int x = q[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adjv[x][k];
                if (col[y] == -1) {
                    col[y] = 1 - col[x];
                    q[qt++] = y;
                } else if (col[y] == col[x]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    long cur = cost_full();
    if (cur == 0) snapshot();
    long stall = 0, iters = 0;
    while (1) {
        if ((iters & 31) == 0 && elapsed() >= tlimit) break;
        iters++;
        if (cur == 0) {
            if (!have_best || n > bestn) snapshot();
            add_vertex();
            fill_edges();
            cur = cost_full();
            stall = 0;
            continue;
        }
        if (!try_switch()) {
            stall++;
        } else {
            long nc = cost_full();
            long delta = nc - cur;
            if (delta <= 0 || rndu() < exp(-(double)delta / TEMP)) cur = nc;
            else undo_switch();
            stall++;
        }
        if (stall > STALL && have_best) {
            restore();
            cur = 0;
            stall = 0;
        }
    }
    if (cur == 0 && (!have_best || n > bestn)) snapshot();
    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bu[i], bv[i]);
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

    Degree is q + 1, diameter is 4, order is 2(q+1)(q^2+1).
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
# Spare-slot matching on a point-line base (GQ base for D >= 4).
# ----------------------------------------------------------------------------

def _spare_matching_base(n0, e0, d, rng, keep_free):
    n = n0
    half = n // 2
    adj = _to_sets(n, e0)
    rounds = d - max(len(a) for a in adj)
    for _ in range(max(0, rounds)):
        order = [p for p in range(half) if len(adj[p]) < d]
        rng.shuffle(order)
        target = max(0, len(order) - keep_free)
        count = 0
        for p in order:
            if count >= target:
                break
            cands = [L for L in range(half, n) if len(adj[L]) < d and L not in adj[p]]
            if not cands:
                continue
            L = rng.choice(cands)
            adj[p].add(L)
            adj[L].add(p)
            count += 1
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


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
# Main build: structured base, short Python trials, then the C annealer
# (bitset bad-pair cost, cover-greedy vertex insertion, snapshot revert)
# takes almost all of the remaining budget.
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

    base_n, base_e = best_n, list(best_e)
    base_is_gq = False
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is not None:
            base_is_gq = True
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.14 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if base_is_gq and D >= 4:
        spare_end = start + 0.18 * time_limit
        while time.monotonic() < spare_end:
            keep = rng.choice((0, 2, 4, 8, 12, 20))
            sn, se = _spare_matching_base(base_n, base_e, d, rng, keep)
            gn, ge = _grow(sn, se, d, D, spare_end, rng)
            consider(gn, ge)

    # C annealer from the best valid graph found so far.
    if D >= 2 and d <= 64 and best_n < lib.moore_bound(d, D):
        c_end = start + 0.90 * time_limit
        budget = c_end - time.monotonic() - 1.5
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 15)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
