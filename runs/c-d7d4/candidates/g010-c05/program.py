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

#define MAXN 6000
#define MAXD 40

static int N, DMAX, DIAM;
static int adj[MAXN][MAXD];
static int dg[MAXN];
static int col[MAXN];
static int bad_adj[MAXN][MAXD];
static int bad_dg[MAXN];
static int bad_N;
static int snap_adj[MAXN][MAXD];
static int snap_dg[MAXN];
static int snap_col[MAXN];
static int snap_N;
static int qbuf[MAXN];
static int seen[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec; }

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) { adj[a][dg[a]++] = b; adj[b][dg[b]++] = a; }
static void del_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--dg[a]]; break; }
    for (int i = 0; i < dg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--dg[b]]; break; }
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long cost(void) {
    long bad = 0;
    if (stamp >= 2000000000) { memset(seen, 0, sizeof(seen)); stamp = 0; }
    for (int s = 0; s < N; s++) {
        stamp++;
        int head = 0, t = 0, depth = 0;
        qbuf[t++] = s; seen[s] = stamp;
        while (head < t && depth < DIAM) {
            int lim = t;
            while (head < lim) {
                int u = qbuf[head++];
                for (int i = 0; i < dg[u]; i++) {
                    int w = adj[u][i];
                    if (seen[w] != stamp) { seen[w] = stamp; qbuf[t++] = w; }
                }
            }
            depth++;
        }
        bad += N - t;
    }
    return bad / 2;
}

static void color_graph(void) {
    for (int i = 0; i < N; i++) col[i] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int head = 0, t = 0;
        qbuf[t++] = s;
        while (head < t) {
            int u = qbuf[head++];
            for (int i = 0; i < dg[u]; i++) {
                int w = adj[u][i];
                if (col[w] == -1) { col[w] = 1 - col[u]; qbuf[t++] = w; }
            }
        }
    }
}

static int read_graph(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n >= MAXN - 2) return 0;
    N = n;
    memset(dg, 0, sizeof(dg));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (dg[u] >= DMAX || dg[v] >= DMAX || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    return 1;
}

static void save_snap(void) {
    snap_N = N;
    for (int i = 0; i < N; i++) {
        snap_dg[i] = dg[i];
        snap_col[i] = col[i];
        memcpy(snap_adj[i], adj[i], sizeof(int) * (size_t)dg[i]);
    }
}
static void restore_snap(void) {
    N = snap_N;
    for (int i = 0; i < N; i++) {
        dg[i] = snap_dg[i];
        col[i] = snap_col[i];
        memcpy(adj[i], snap_adj[i], sizeof(int) * (size_t)dg[i]);
    }
}
static void save_best(void) {
    bad_N = N;
    for (int i = 0; i < N; i++) {
        bad_dg[i] = dg[i];
        memcpy(bad_adj[i], adj[i], sizeof(int) * (size_t)dg[i]);
    }
}
static void print_best(void) {
    long m = 0;
    for (int u = 0; u < bad_N; u++) m += bad_dg[u];
    m /= 2;
    printf("%d %ld\n", bad_N, m);
    for (int u = 0; u < bad_N; u++)
        for (int k = 0; k < bad_dg[u]; k++) {
            int v = bad_adj[u][k];
            if (u < v) printf("%d %d\n", u, v);
        }
}

/* Add cross-side edges between deficient vertices (random sampling). */
static void fill_edges(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int x = 0; x < N; x++) {
        if (dg[x] < DMAX) {
            if (col[x] == 0) L0[n0++] = x; else L1[n1++] = x;
        }
    }
    if (n0 == 0 || n1 == 0) return;
    long tries = 4L * (n0 + n1) + 10;
    for (long t = 0; t < tries; t++) {
        int a = L0[rnd_int(n0)], b = L1[rnd_int(n1)];
        if (dg[a] < DMAX && dg[b] < DMAX && !has_edge(a, b)) add_edge(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static long anneal(long cur, int iters, double deadline) {
    static int S0[MAXN];
    int n0 = 0;
    for (int x = 0; x < N; x++) if (col[x] == 0) S0[n0++] = x;
    if (n0 == 0) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now_s() > deadline) break;
        int a = S0[rnd_int(n0)];
        if (dg[a] == 0) continue;
        int b = adj[a][rnd_int(dg[a])];
        int c = S0[rnd_int(n0)];
        if (c == a || dg[c] == 0) continue;
        int e = adj[c][rnd_int(dg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd_int(10) == 0)) {
            cur = nw;
        } else {
            del_edge(a, e); del_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double tl = atof(argv[4]);
    DMAX = d < MAXD ? d : MAXD;
    double deadline = now_s() + tl;

    if (!read_graph()) { printf("0 0\n"); return 0; }
    color_graph();
    save_best();
    if (DIAM < 2 || DMAX < 2) { print_best(); return 0; }

    static int cand[MAXN];
    while (now_s() < deadline) {
        if (N >= MAXN - 2) break;
        save_snap();
        int side = rnd_int(2);
        int cn = 0;
        for (int x = 0; x < N; x++) if (col[x] == side) cand[cn++] = x;
        int v = N;
        N++;
        dg[v] = 0;
        col[v] = 1 - side;
        int k = DMAX < cn ? DMAX : cn;
        for (int i = 0; i < k; i++) {
            int j = i + rnd_int(cn - i);
            int tmp = cand[i]; cand[i] = cand[j]; cand[j] = tmp;
            int s = cand[i];
            if (dg[s] >= DMAX) {
                int t = adj[s][rnd_int(dg[s])];
                del_edge(s, t);
            }
            add_edge(s, v);
        }
        fill_edges();
        long cur = cost();
        if (cur > 0) cur = anneal(cur, 300, deadline);
        if (cur == 0) {
            if (N > bad_N) save_best();
        } else {
            restore_snap();
        }
    }
    print_best();
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
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
# Random voltage lifts of small d-regular bipartite base multigraphs.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts slightly above best_n, repair them, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


# ----------------------------------------------------------------------------
# C kill-free repair: add a vertex, anneal the bad pairs away, keep if valid.
# ----------------------------------------------------------------------------

def _c_repair(d, D, n, edges, seed, start, time_limit, consider):
    """Run the C engine from the current best graph; consider its output."""
    remaining = start + 0.85 * time_limit - time.monotonic()
    if remaining < 2.0:
        return
    budget = 0.7 * remaining
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3)],
                        stdin_graph=(n, edges), timeout=remaining)
        n2, e2 = lib.parse_graph_text(out)
        consider(n2, e2)
    except Exception:
        pass


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

    try:
        # Structured base: W(q) for D >= 4, PG(2,q) for D = 3.
        base_n, base_e = best_n, list(best_e)
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
                consider(n1, e1)

        if D >= 2:
            # Randomized twin-duplication pipelines from the structured base.
            trial_end = start + 0.22 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)

            # Random voltage lifts of small bipartite base multigraphs.
            lift_end = start + 0.3 * time_limit
            _lift_search(d, D, lift_end, rng, best_n, consider)

            # C annealing repair from the best valid graph found so far.
            _c_repair(d, D, best_n, best_e, seed, start, time_limit, consider)
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
