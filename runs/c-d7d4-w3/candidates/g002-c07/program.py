import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 40
#define MAXW (MAXN / 64)
#define ITERS 1500

static int N, D, DL;
static int deg[MAXN];
static int adjv[MAXN][MAXDEG];
static int side[MAXN];

static int sN, sdeg[MAXN], sadj[MAXN][MAXDEG], sside[MAXN];
static int bN, bdeg[MAXN], badj[MAXN][MAXDEG], bside[MAXN];

static uint64_t bufX[MAXN * MAXW], bufY[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double budget;

static uint64_t xr(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int n) { return (int)(xr() % (uint64_t)n); }
static double rnd01(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC >= budget;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int j = 0; j < deg[u]; j++) if (adjv[u][j] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adjv[u][deg[u]++] = v;
    adjv[v][deg[v]++] = u;
}
static void del_arc(int u, int v) {
    for (int j = 0; j < deg[u]; j++) {
        if (adjv[u][j] == v) {
            adjv[u][j] = adjv[u][--deg[u]];
            return;
        }
    }
}
static void del_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Bitmask balls of radius r around every vertex (flat, stride W). */
static uint64_t *balls(int r) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufX, *nxt = bufY;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *s = cur + (size_t)adjv[v][j] * W;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered vertex pairs at distance more than D. */
static long cost(void) {
    int W = (N + 63) / 64;
    uint64_t *b = balls(D);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *bv = b + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(bv[w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Add a vertex on side 1-sd joined to a greedy cover of side sd by radius D-1 balls. */
static void add_vertex(int sd) {
    int W = (N + 63) / 64;
    uint64_t *b = balls(D - 1);
    uint64_t cov[MAXW];
    int chosen[MAXDEG];
    int nc = 0;
    memset(cov, 0, sizeof cov);
    for (int it = 0; it < DL; it++) {
        int best = -1;
        double bsc = -1.0;
        for (int s = 0; s < N; s++) {
            if (side[s] != sd) continue;
            int used = 0;
            for (int k = 0; k < nc; k++) if (chosen[k] == s) { used = 1; break; }
            if (used) continue;
            const uint64_t *bs = b + (size_t)s * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(bs[w] & ~cov[w]);
            if (g == 0) continue;
            double sc = g + 0.5 * rnd01();
            if (sc > bsc) { bsc = sc; best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        const uint64_t *bb = b + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= bb[w];
    }
    if (nc == 0 || N >= MAXN - 1) return;
    int v = N++;
    side[v] = 1 - sd;
    deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= DL) {
            int t = adjv[s][rnd(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* Join deficient opposite-side vertices in random order. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DL) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) { int j = rnd(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = nr - 1; i > 0; i--) { int j = rnd(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t; }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= DL) break;
            int b = R[j];
            if (deg[b] < DL && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. True if cost reaches 0. */
static int anneal(int iters) {
    long cur = cost();
    static int S0[MAXN];
    int ns = 0;
    for (int v = 0; v < N; v++) if (side[v] == 0) S0[ns++] = v;
    if (ns == 0) return cur == 0;
    for (int it = 0; it < iters; it++) {
        if (cur == 0) break;
        if ((it & 15) == 0 && timeup()) break;
        int a = S0[rnd(ns)];
        if (deg[a] == 0) continue;
        int b = adjv[a][rnd(deg[a])];
        int c = S0[rnd(ns)];
        if (c == a || deg[c] == 0) continue;
        int e = adjv[c][rnd(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.1)) {
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

static void snapshot(void) {
    sN = N;
    memcpy(sdeg, deg, sizeof deg);
    memcpy(sadj, adjv, sizeof adjv);
    memcpy(sside, side, sizeof side);
}
static void restore(void) {
    N = sN;
    memcpy(deg, sdeg, sizeof deg);
    memcpy(adjv, sadj, sizeof adjv);
    memcpy(side, sside, sizeof side);
}
static void keep_best(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof deg);
    memcpy(badj, adjv, sizeof adjv);
    memcpy(bside, side, sizeof side);
}

static int color_graph(void) {
    static int st[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int top = 0;
        st[top++] = s;
        while (top > 0) {
            int u = st[--top];
            for (int j = 0; j < deg[u]; j++) {
                int v = adjv[u][j];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    st[top++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    t0 = clock();
    DL = d;
    if (d < 1 || d > MAXDEG || D < 2) { puts("0 0"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        if (2 * d > MAXN) { puts("0 0"); return 0; }
        N = 2 * d;
        for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = v < d ? 0 : 1; }
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) add_edge(i, d + j);
    } else {
        if (n > MAXN - 1) { puts("0 0"); return 0; }
        N = n;
        for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = -1; }
        int bad = 0;
        for (int k = 0; k < m; k++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
            if (u < 0 || u >= N || v < 0 || v >= N || u == v ||
                deg[u] >= DL || deg[v] >= DL || has_edge(u, v)) {
                bad = 1;
            } else {
                add_edge(u, v);
            }
        }
        if (bad || !color_graph()) { puts("0 0"); return 0; }
    }

    fill();
    if (!anneal(ITERS * 10)) { puts("0 0"); return 0; }
    keep_best();

    while (!timeup()) {
        if (N >= MAXN - 1) break;
        snapshot();
        add_vertex(rnd(2));
        fill();
        if (anneal(ITERS)) {
            if (N > bN) keep_best();
        } else {
            restore();
        }
    }

    int M = 0;
    for (int v = 0; v < bN; v++) M += bdeg[v];
    M /= 2;
    printf("%d %d\n", bN, M);
    for (int v = 0; v < bN; v++)
        for (int j = 0; j < bdeg[v]; j++)
            if (v < badj[v][j]) printf("%d %d\n", v, badj[v][j]);
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
# Shared Python helpers (growth by cover vertices, saturation, twins).
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
# Main build: structured base, short Python trials, then C annealing repair.
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pass from the best base.
    if D >= 2:
        trial_end = start + 0.18 * time_limit
        base_n, base_e = best_n, list(best_e)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # C annealing repair: add vertices one at a time and repair with degree-preserving switches.
    if D >= 2:
        c_end = start + 0.85 * time_limit
        now = time.monotonic()
        c_budget = c_end - now - 1.0
        if c_budget > 0.5:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}"],
                                stdin_graph=(best_n, best_e),
                                timeout=c_budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
