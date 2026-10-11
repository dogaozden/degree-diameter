import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite simulated annealing that grows a valid graph one vertex
# at a time. Each step adds a vertex, repairs the diameter with degree-preserving
# double-edge switches and endpoint moves, and keeps the result only if the
# number of pairs at distance > D reaches zero. Every saved state is valid.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static int d, D, cap, n;
static int *side, *deg, *adj, *tmpv, *bq;
static int *snap_side, *snap_deg, *snap_adj, snap_n;
static u64 *bufA, *bufB;
static u64 rng_s;
static double t_end;

typedef struct { int t, a, b; } Op;
static Op oplog[16];
static int nlog;

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static u64 rnd(void) {
    rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17;
    return rng_s;
}
static int rndint(int m) { return (int)(rnd() % (u64)m); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void fail_out(void) { printf("0 0\n"); exit(0); }

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++) if (p[k] == b) return 1;
    return 0;
}

static void add_edge_raw(int a, int b) {
    adj[(size_t)a * d + deg[a]++] = b;
    adj[(size_t)b * d + deg[b]++] = a;
}

static void rem_one(int a, int b) {
    int *p = adj + (size_t)a * d;
    for (int k = 0; k < deg[a]; k++) {
        if (p[k] == b) { p[k] = p[deg[a] - 1]; deg[a]--; return; }
    }
}

static void del_edge_raw(int a, int b) { rem_one(a, b); rem_one(b, a); }

static void op_add(int a, int b) {
    add_edge_raw(a, b);
    oplog[nlog].t = 0; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}
static void op_del(int a, int b) {
    del_edge_raw(a, b);
    oplog[nlog].t = 1; oplog[nlog].a = a; oplog[nlog].b = b; nlog++;
}
static void undo(void) {
    while (nlog > 0) {
        nlog--;
        Op o = oplog[nlog];
        if (o.t == 0) del_edge_raw(o.a, o.b);
        else add_edge_raw(o.a, o.b);
    }
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long long cost(void) {
    int W = (n + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(u64) * W);
            const int *p = adj + (size_t)v * d;
            for (int k = 0; k < deg[v]; k++) {
                const u64 *x = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= x[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        const u64 *c = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

/* One random local move. Returns 0 if no move was applied (nothing logged). */
static int do_move(void) {
    int mv = rndint(100);
    if (mv < 45) {
        /* double-edge switch on the bipartition: a-b, c-e -> a-e, c-b */
        int a = rndint(n);
        if (side[a] != 0 || deg[a] == 0) return 0;
        int b = adj[(size_t)a * d + rndint(deg[a])];
        int c = rndint(n);
        if (side[c] != 0 || c == a || deg[c] == 0) return 0;
        int e = adj[(size_t)c * d + rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) return 0;
        op_del(a, b); op_del(c, e); op_add(a, e); op_add(c, b);
        return 1;
    }
    if (mv < 75) {
        if (rnd() & 1) {
            /* move side-1 endpoint of an edge onto a deficient side-1 vertex */
            int a = rndint(n);
            if (side[a] != 0 || deg[a] == 0) return 0;
            int b = adj[(size_t)a * d + rndint(deg[a])];
            int e = rndint(n);
            if (side[e] != 1 || e == b || deg[e] >= d) return 0;
            if (has_edge(a, e)) return 0;
            op_del(a, b); op_add(a, e);
            return 1;
        } else {
            /* move side-0 endpoint of an edge onto a deficient side-0 vertex */
            int b = rndint(n);
            if (side[b] != 1 || deg[b] == 0) return 0;
            int a = adj[(size_t)b * d + rndint(deg[b])];
            int f = rndint(n);
            if (side[f] != 0 || f == a || deg[f] >= d) return 0;
            if (has_edge(f, b)) return 0;
            op_del(a, b); op_add(f, b);
            return 1;
        }
    }
    if (mv < 92) {
        /* add an edge between two deficient vertices on opposite sides */
        int a = rndint(n), b = rndint(n);
        if (side[a] == side[b] || deg[a] >= d || deg[b] >= d || has_edge(a, b)) return 0;
        if (side[a] == 1) { int t = a; a = b; b = t; }
        op_add(a, b);
        return 1;
    }
    /* remove a random edge */
    {
        int a = rndint(n);
        if (deg[a] == 0) return 0;
        int b = adj[(size_t)a * d + rndint(deg[a])];
        op_del(a, b);
        return 1;
    }
}

/* Simulated annealing on the bad-pair count. Returns final cost (0 means valid). */
static long long anneal(long iters, double T0, double T1) {
    long long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        nlog = 0;
        if (!do_move()) continue;
        long long nc = cost();
        long long dl = nc - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = nc;
        else undo();
    }
    return cur;
}

/* Add vertex v on side s, joined to deficient opposite vertices; then steal
   neighbours from full opposite vertices to fill its remaining degree. */
static void add_vertex(int s) {
    int v = n++;
    side[v] = s; deg[v] = 0;
    int nc = 0;
    for (int u = 0; u < v; u++) if (side[u] != s && deg[u] < d) tmpv[nc++] = u;
    for (int i = 0; i < nc && deg[v] < d; i++) {
        int j = i + rndint(nc - i);
        int t = tmpv[i]; tmpv[i] = tmpv[j]; tmpv[j] = t;
        add_edge_raw(v, tmpv[i]);
    }
    int tries = 0;
    while (deg[v] < d && tries < 20000) {
        tries++;
        int x = rndint(v);
        if (side[x] == s || deg[x] == 0 || has_edge(v, x)) continue;
        if (deg[x] < d) {
            add_edge_raw(x, v);
        } else {
            int y = adj[(size_t)x * d + rndint(deg[x])];
            del_edge_raw(x, y);
            add_edge_raw(x, v);
        }
    }
}

static void snapshot(void) {
    snap_n = n;
    memcpy(snap_side, side, sizeof(int) * n);
    memcpy(snap_deg, deg, sizeof(int) * n);
    memcpy(snap_adj, adj, sizeof(int) * (size_t)n * d);
}

static void restore(void) {
    n = snap_n;
    memcpy(side, snap_side, sizeof(int) * n);
    memcpy(deg, snap_deg, sizeof(int) * n);
    memcpy(adj, snap_adj, sizeof(int) * (size_t)n * d);
}

static void emit(void) {
    long long m = 0;
    for (int v = 0; v < snap_n; v++)
        for (int k = 0; k < snap_deg[v]; k++)
            if (snap_adj[(size_t)v * d + k] > v) m++;
    printf("%d %lld\n", snap_n, m);
    for (int v = 0; v < snap_n; v++)
        for (int k = 0; k < snap_deg[v]; k++) {
            int u = snap_adj[(size_t)v * d + k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rng_s = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (!rng_s) rng_s = 1;
    double budget = atof(argv[4]);
    t_end = now() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || m0 < 0 || d < 2 || D < 1) fail_out();
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) fail_out();

    /* Moore-type bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i. */
    double bnd = 0, p = 1;
    for (int i = 0; i < D; i++) { bnd += p; p *= (d - 1); if (bnd > 1e9) break; }
    bnd *= 2;
    double capd = bnd < (double)n0 + 4000.0 ? bnd : (double)n0 + 4000.0;
    cap = (int)capd;
    if (cap < n0) cap = n0;
    int W = (cap + 63) >> 6;

    side = malloc(sizeof(int) * (size_t)cap);
    deg = calloc((size_t)cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    tmpv = malloc(sizeof(int) * (size_t)cap);
    bq = malloc(sizeof(int) * (size_t)cap);
    snap_side = malloc(sizeof(int) * (size_t)cap);
    snap_deg = malloc(sizeof(int) * (size_t)cap);
    snap_adj = malloc(sizeof(int) * (size_t)cap * d);
    bufA = malloc(sizeof(u64) * (size_t)cap * W);
    bufB = malloc(sizeof(u64) * (size_t)cap * W);

    n = n0;
    for (int i = 0; i < m0; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || b < 0 || a >= n || b >= n || a == b) fail_out();
        if (has_edge(a, b)) continue;
        if (deg[a] >= d || deg[b] >= d) fail_out();
        add_edge_raw(a, b);
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        bq[qt++] = s;
        while (qh < qt) {
            int v = bq[qh++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[(size_t)v * d + k];
                if (side[u] == -1) { side[u] = 1 - side[v]; bq[qt++] = u; }
                else if (side[u] == side[v]) fail_out();
            }
        }
    }

    long long c0 = cost();
    if (c0 > 0) c0 = anneal(400000, 1.0, 0.05);
    if (c0 > 0) fail_out();
    snapshot();

    int iters_base = 3000, iters = iters_base, fails = 0;
    while (now() < t_end && n < cap) {
        int s = rndint(2);
        add_vertex(s);
        long long c = anneal(iters, 1.0, 0.05);
        if (c == 0) {
            snapshot();
            fails = 0;
            iters = iters_base;
        } else {
            restore();
            fails++;
            if (fails % 10 == 0 && iters < 200000) iters *= 2;
            if (fails > 1000) break;
        }
    }
    emit();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions and helpers (kept from the previous pipeline).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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
# Driver. Python builds a short structured start (about 15% of the budget),
# then the C annealing engine grows it for most of the remaining time.
# Every candidate passes lib.is_valid before it is kept. K_{d,d}-style
# haar_graph(d, range(d)) is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    rng = random.Random(seed)

    # Python phase: structured base, then short randomized trials.
    if D >= 2:
        py_end = start + 0.15 * time_limit
        base = None
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, py_end, rng)
            consider(n1, e1)
        while time.monotonic() < py_end:
            n, e = _trial(best_n, best_e, d, D, rng, py_end)
            consider(n, e)

    # C phase: anneal-based vertex growth from the best valid start.
    if D >= 2 and d >= 2:
        c_budget = 0.80 * time_limit - (time.monotonic() - start) - 1.0
        if c_budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=c_budget + 10.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
