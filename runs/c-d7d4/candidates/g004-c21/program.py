import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: cost-driven ILS over bipartite switches with bitset balls.
# Repeatedly adds a vertex (greedy cover of the other side, then annealing)
# or kicks random edges, repairs by annealing, and keeps every valid result.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1536
#define MAXW 24
#define MAXD 60
#define ITERS 1500

static int N, DM, DIAM, BN, CN;
static int deg[MAXN], col[MAXN];
static int adj[MAXN][MAXD];
static int cdeg[MAXN], ccol[MAXN], cadj[MAXN][MAXD];
static int bdeg[MAXN], badj[MAXN][MAXD];
static uint64_t RB[MAXN * MAXW], TB[MAXN * MAXW], BALL[MAXN * MAXW];
static int side0[MAXN];
static int qbuf[MAXN];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int u, int v) {
    for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
    return 0;
}
static void del_arc(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) { adj[u][k] = adj[u][--deg[u]]; return; }
    }
}
static void add_edge(int u, int v) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* out[v] = bitset of vertices within distance r of v */
static void reach(int r, uint64_t *out) {
    int n = N, w = (n + 63) >> 6;
    uint64_t *cur = out, *nxt = TB;
    memset(out, 0, sizeof(uint64_t) * (size_t)n * w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *x = nxt + (size_t)v * w;
            const uint64_t *cv = cur + (size_t)v * w;
            memcpy(x, cv, sizeof(uint64_t) * w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *cu = cur + (size_t)adj[v][k] * w;
                for (int t = 0; t < w; t++) x[t] |= cu[t];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)n * w);
}

/* number of unordered pairs at distance > DIAM (unreachable counts) */
static long long cost(void) {
    int n = N, w = (n + 63) >> 6;
    reach(DIAM, RB);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *rv = RB + (size_t)v * w;
        for (int t = 0; t < w; t++) c += __builtin_popcountll(rv[t]);
        bad += n - c;
    }
    return bad / 2;
}

/* bipartite double-edge switches minimising cost; returns 1 if cost reaches 0 */
static int anneal(int iters, clock_t tend) {
    int ns = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0) side0[ns++] = v;
    if (ns < 2) return 0;
    long long cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && clock() > tend) break;
        int a = side0[rndint(ns)];
        if (deg[a] == 0) continue;
        int b = adj[a][rndint(deg[a])];
        int c = side0[rndint(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.1)) {
            cur = nw;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur == 0;
}

/* join deficient opposite-side vertices at random */
static void fill(void) {
    int tries = 40 * N;
    for (int t = 0; t < tries; t++) {
        int a = rndint(N), b = rndint(N);
        if (col[a] == col[b] || deg[a] >= DM || deg[b] >= DM) continue;
        if (col[a] == 1) { int tmp = a; a = b; b = tmp; }
        if (has_edge(a, b)) continue;
        add_edge(a, b);
    }
}

/* new vertex on the opposite side of `side`, joined to a greedy cover of `side` */
static int add_vertex(int side) {
    static int cand[MAXN];
    static int chosen[MAXD];
    static char used[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++) if (col[v] == side) cand[nc++] = v;
    if (nc < DM || N >= MAXN - 1) return 0;
    int w = (N + 63) >> 6;
    reach(DIAM - 1, BALL);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof cov);
    memset(used, 0, sizeof used);
    int nch = 0;
    for (int step = 0; step < DM; step++) {
        int best = -1;
        double bs = -1.0;
        for (int i = 0; i < nc; i++) {
            int s = cand[i];
            if (used[s]) continue;
            const uint64_t *b = BALL + (size_t)s * w;
            int g = 0;
            for (int t = 0; t < w; t++) g += __builtin_popcountll(b[t] & ~cov[t]);
            double sc = g + 0.5 * rnd01();
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const uint64_t *bb = BALL + (size_t)best * w;
        for (int t = 0; t < w; t++) cov[t] |= bb[t];
    }
    int v = N++;
    deg[v] = 0;
    col[v] = 1 - side;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg[s] >= DM) {
            int t = adj[s][rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

/* delete k random edges */
static void kick_edges(int k) {
    for (int i = 0; i < k; i++) {
        for (int tries = 0; tries < 50; tries++) {
            int v = rndint(N);
            if (deg[v] == 0) continue;
            int u = adj[v][rndint(deg[v])];
            del_edge(v, u);
            break;
        }
    }
}

static void save_cur(void) {
    CN = N;
    memcpy(cdeg, deg, sizeof deg);
    memcpy(ccol, col, sizeof col);
    memcpy(cadj, adj, sizeof adj);
}
static void load_cur(void) {
    N = CN;
    memcpy(deg, cdeg, sizeof deg);
    memcpy(col, ccol, sizeof col);
    memcpy(adj, cadj, sizeof adj);
}
static void save_best(void) {
    BN = N;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(badj, adj, sizeof adj);
}

static void emit(int n, const int *dg, int (*ad)[MAXD]) {
    long long m = 0;
    for (int v = 0; v < n; v++) m += dg[v];
    printf("%d %lld\n", n, m / 2);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < dg[v]; k++)
            if (v < ad[v][k]) printf("%d %d\n", v, ad[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    clock_t tend = clock() + (clock_t)(tl * 0.95 * CLOCKS_PER_SEC);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > MAXN - 64 || m0 < 0 ||
        d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n0; DM = d; DIAM = D;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
            deg[u] >= DM || deg[v] >= DM || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) { col[w] = 1 - col[u]; qbuf[qt++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    if (cost() != 0 && !anneal(200000, tend)) { printf("0 0\n"); return 0; }

    save_cur();
    save_best();
    while (clock() < tend) {
        load_cur();
        if (rndint(10) < 7) {
            if (!add_vertex(rndint(2))) kick_edges(1 + rndint(4));
        } else {
            kick_edges(1 + rndint(6));
        }
        fill();
        if (anneal(ITERS, tend)) {
            save_cur();
            if (N > BN) save_best();
        }
    }
    emit(BN, bdeg, badj);
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

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers.
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
    """Greedily add vertices whose neighbourhoods cover the other side's balls."""
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
    """Join deficient opposite-side vertices in random order (keeps bipartite, only shortens paths)."""
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
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
# Python fallback repair (used only if the C engine is unavailable).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
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


def _repair(d, D, n, edges, deadline, rng, consider):
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        _add_vertex(adj, color, d, D, rng.randrange(2), rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# C engine driver.
# ----------------------------------------------------------------------------

def _run_c_polish(d, D, n, edges, seed, budget):
    """Run the C ILS on a valid graph. Returns (n, edges) or None on any failure."""
    if budget < 0.5 or d > 60 or D < 2 or n < 2:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(n, edges), timeout=budget + 3.0)
        return lib.parse_graph_text(out)
    except Exception:
        return None


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

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
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

    # Short randomized twin/cover pipelines from the base or the best so far.
    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            if best_n > base_n and rng.random() < 0.5:
                bn, be = best_n, list(best_e)
            else:
                bn, be = base_n, list(base_e)
            n, e = _trial(bn, be, d, D, rng, trial_end)
            consider(n, e)

    # Main stage: C ILS from the best valid graph found so far.
    if D >= 2:
        c_budget = deadline - time.monotonic() - 1.0
        res = _run_c_polish(d, D, best_n, best_e, seed, c_budget)
        if res is not None:
            consider(res[0], res[1])

    # Python fallback if time remains (for example, if the C stage failed).
    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
