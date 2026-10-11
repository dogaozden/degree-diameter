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

typedef uint64_t u64;

#define ITERS_GROW 1500
#define ITERS_KICK 2500

static int d, D, cap, W, n;
static long long moore;
static int *deg, *adj, *col;
static u64 *bA, *bT, *bC;
static int *L0, *L1, n0c, n1c;
static int *gDeg, *gAdj, *gCol, gN;
static int *bDeg, *bAdj, *bCol, bN;
static u64 rs = 0x9E3779B97F4A7C15ULL;
static clock_t deadline;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int m) { return (int)(rnd() % (u64)m); }
static double rndf(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a * d + k] == b) return 1;
    return 0;
}

static void push_edge(int a, int b) {
    adj[a * d + deg[a]++] = b;
    adj[b * d + deg[b]++] = a;
}

static void repl(int x, int old, int nw) {
    int *p = adj + x * d;
    for (int k = 0; k < deg[x]; k++) if (p[k] == old) { p[k] = nw; return; }
}

static void drop_edge(int a, int b) {
    int *p = adj + a * d;
    for (int k = 0; k < deg[a]; k++) if (p[k] == b) { p[k] = p[--deg[a]]; break; }
    p = adj + b * d;
    for (int k = 0; k < deg[b]; k++) if (p[k] == a) { p[k] = p[--deg[b]]; break; }
}

/* out[v] = bitset of vertices within distance r of v (stride W). */
static void balls(int r, u64 *out) {
    int w = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        u64 *o = out + (size_t)v * W;
        for (int i = 0; i < w; i++) o[i] = 0;
        o[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            u64 *t = bT + (size_t)v * W;
            const u64 *o = out + (size_t)v * W;
            for (int i = 0; i < w; i++) t[i] = o[i];
            for (int k = 0; k < deg[v]; k++) {
                const u64 *x = out + (size_t)adj[v * d + k] * W;
                for (int i = 0; i < w; i++) t[i] |= x[i];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(out + (size_t)v * W, bT + (size_t)v * W, sizeof(u64) * w);
    }
}

/* Number of unordered vertex pairs at distance > D (unreachable pairs included). */
static long long bad_pairs(void) {
    int w = (n + 63) >> 6;
    balls(D, bA);
    long long s = 0;
    for (int v = 0; v < n; v++) {
        const u64 *r = bA + (size_t)v * W;
        for (int i = 0; i < w; i++) s += popc(r[i]);
    }
    return ((long long)n * n - s) / 2;
}

static void build_sides(void) {
    n0c = n1c = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] == 0) L0[n0c++] = v;
        else L1[n1c++] = v;
    }
}

/* Random degree-preserving bipartite double-edge switch. */
static int try_switch(int *sw) {
    if (n0c < 2) return 0;
    int a = L0[rndi(n0c)];
    if (deg[a] == 0) return 0;
    int b = adj[a * d + rndi(deg[a])];
    int c = L0[rndi(n0c)];
    if (c == a || deg[c] == 0) return 0;
    int e = adj[c * d + rndi(deg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    repl(a, b, e); repl(e, c, a); repl(c, e, b); repl(b, a, c);
    sw[0] = a; sw[1] = b; sw[2] = c; sw[3] = e;
    return 1;
}

static void undo_switch(const int *sw) {
    int a = sw[0], b = sw[1], c = sw[2], e = sw[3];
    repl(a, e, b); repl(b, c, a); repl(c, b, e); repl(e, a, c);
}

/* Simulated annealing on switches, minimising bad pairs at fixed n. Returns final cost. */
static long long anneal(int iters, double T0, double T1) {
    build_sides();
    long long cur = bad_pairs();
    if (cur == 0 || n0c < 2 || n1c < 1) return cur;
    int sw[4];
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        if (!try_switch(sw)) continue;
        long long nw = bad_pairs();
        if (nw <= cur || rndf() < exp(-(double)(nw - cur) / T)) cur = nw;
        else undo_switch(sw);
    }
    return cur;
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add cross edges between deficient vertices of opposite sides (never hurts distances). */
static void fill(void) {
    build_sides();
    int *D0 = malloc(sizeof(int) * (n + 1));
    int *D1 = malloc(sizeof(int) * (n + 1));
    int c0 = 0, c1 = 0;
    for (int i = 0; i < n0c; i++) if (deg[L0[i]] < d) D0[c0++] = L0[i];
    for (int i = 0; i < n1c; i++) if (deg[L1[i]] < d) D1[c1++] = L1[i];
    shuffle(D0, c0);
    shuffle(D1, c1);
    for (int i = 0; i < c0; i++) {
        int a = D0[i];
        for (int j = 0; j < c1 && deg[a] < d; j++) {
            int b = D1[j];
            if (deg[b] < d && !has_edge(a, b)) push_edge(a, b);
        }
    }
    free(D0);
    free(D1);
}

/* Add a vertex on a random side, joined greedily to a cover of the other side's balls. */
static int add_vertex(void) {
    if (n >= moore || n >= cap) return 0;
    int c = rndi(2);
    int w = (n + 63) >> 6;
    balls(D - 1, bA);
    for (int i = 0; i < w; i++) bC[i] = 0;
    int *chosen = malloc(sizeof(int) * (size_t)d);
    int nch = 0;
    for (int pick = 0; pick < d; pick++) {
        int best = -1, bestg = -1;
        double bsc = -1.0;
        for (int s = 0; s < n; s++) {
            if (col[s] != 1 - c) continue;
            int used = 0;
            for (int j = 0; j < nch; j++) if (chosen[j] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            const u64 *r = bA + (size_t)s * W;
            for (int i = 0; i < w; i++) g += popc(r[i] & ~bC[i]);
            double sc = g + 0.5 * rndf();
            if (sc > bsc) { bsc = sc; best = s; bestg = g; }
        }
        if (best < 0 || bestg == 0) break;
        chosen[nch++] = best;
        const u64 *r = bA + (size_t)best * W;
        for (int i = 0; i < w; i++) bC[i] |= r[i];
    }
    if (nch == 0) { free(chosen); return 0; }
    int v = n;
    n++;
    deg[v] = 0;
    col[v] = c;
    for (int j = 0; j < nch; j++) {
        int s = chosen[j];
        if (deg[s] >= d) {
            int t = adj[s * d + rndi(deg[s])];
            drop_edge(s, t);
        }
        push_edge(s, v);
    }
    free(chosen);
    return 1;
}

static void save_to(int *dg, int *ad, int *cl, int *nn) {
    *nn = n;
    memcpy(dg, deg, sizeof(int) * n);
    memcpy(ad, adj, sizeof(int) * (size_t)n * d);
    memcpy(cl, col, sizeof(int) * n);
}

static void load_from(const int *dg, const int *ad, const int *cl, int nn) {
    n = nn;
    memcpy(deg, dg, sizeof(int) * n);
    memcpy(adj, ad, sizeof(int) * (size_t)n * d);
    memcpy(col, cl, sizeof(int) * n);
}

static int check_bip(void) {
    int *st = malloc(sizeof(int) * (n + 1));
    for (int v = 0; v < n; v++) col[v] = -1;
    int ok = 1;
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int top = 0;
        st[top++] = s;
        while (top && ok) {
            int u = st[--top];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u * d + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; st[top++] = v; }
                else if (col[v] == col[u]) { ok = 0; break; }
            }
        }
    }
    free(st);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    if (d < 3 || D < 2) { printf("0 0\n"); return 0; }

    long long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (p > 1000000000LL) p = 1000000000LL;
    }
    moore = 2 * s;
    cap = moore < 20000 ? (int)moore : 20000;
    if (cap < 2 * d) cap = 2 * d;
    W = (cap + 63) / 64;

    deg = calloc(cap, sizeof(int));
    adj = calloc((size_t)cap * d, sizeof(int));
    col = calloc(cap, sizeof(int));
    bA = calloc((size_t)cap * W, sizeof(u64));
    bT = calloc((size_t)cap * W, sizeof(u64));
    bC = calloc(W + 1, sizeof(u64));
    L0 = malloc(sizeof(int) * (cap + 1));
    L1 = malloc(sizeof(int) * (cap + 1));
    gDeg = malloc(sizeof(int) * (cap + 1));
    gAdj = malloc(sizeof(int) * (size_t)(cap + 1) * d);
    gCol = malloc(sizeof(int) * (cap + 1));
    bDeg = malloc(sizeof(int) * (cap + 1));
    bAdj = malloc(sizeof(int) * (size_t)(cap + 1) * d);
    bCol = malloc(sizeof(int) * (cap + 1));

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m0 + 1));
    int ok = (n0 >= 1 && n0 <= cap);
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { ok = 0; break; }
    }
    n = ok ? n0 : 0;
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int a = eu[i], b = ev[i];
            if (a < 0 || b < 0 || a >= n || b >= n || a == b ||
                deg[a] >= d || deg[b] >= d || has_edge(a, b)) ok = 0;
            else push_edge(a, b);
        }
    }
    if (ok) {
        if (!check_bip() || bad_pairs() != 0) ok = 0;
    }
    if (!ok) {
        memset(deg, 0, sizeof(int) * cap);
        n = 2 * d;
        for (int i = 0; i < n; i++) col[i] = i < d ? 0 : 1;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) push_edge(i, d + j);
    }

    deadline = clock() + (clock_t)(limit * CLOCKS_PER_SEC);
    save_to(gDeg, gAdj, gCol, &gN);
    save_to(bDeg, bAdj, bCol, &bN);

    while (clock() < deadline) {
        if (n >= moore || n >= cap) break;
        if (rndf() < 0.75) {
            if (!add_vertex()) {
                load_from(gDeg, gAdj, gCol, gN);
                continue;
            }
            fill();
            long long c = anneal(ITERS_GROW, 1.0, 0.05);
            if (c == 0) {
                save_to(gDeg, gAdj, gCol, &gN);
                if (n > bN) save_to(bDeg, bAdj, bCol, &bN);
            } else {
                load_from(gDeg, gAdj, gCol, gN);
            }
        } else {
            load_from(gDeg, gAdj, gCol, gN);
            build_sides();
            int k = 20 + rndi(60), done = 0;
            int sw[4];
            for (int t = 0; done < k && t < 100 * k; t++)
                if (try_switch(sw)) done++;
            fill();
            long long c = anneal(ITERS_KICK, 0.6, 0.05);
            if (c == 0) save_to(gDeg, gAdj, gCol, &gN);
            else load_from(gDeg, gAdj, gCol, gN);
        }
    }

    long long m = 0;
    for (int v = 0; v < bN; v++) m += bDeg[v];
    m /= 2;
    printf("%d %lld\n", bN, m);
    for (int v = 0; v < bN; v++)
        for (int k = 0; k < bDeg[v]; k++) {
            int u = bAdj[v * d + k];
            if (v < u) printf("%d %d\n", v, u);
        }
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
        if q <= 9 and lib.is_prime_power(q):
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
        # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
        base_n, base_e = best_n, list(best_e)
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                n1, e1 = _grow(n0, e0, d, D, start + 0.04 * time_limit, rng)
                consider(n1, e1)
                base_n, base_e = best_n, list(best_e)

        # Short Python twin-duplication pipelines to seed the C search.
        if D >= 2 and d >= 3:
            trial_end = start + 0.10 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)
    except Exception:
        pass

    # C simulated annealing: grow by one vertex at a time, repair with degree-preserving
    # switches minimising bad pairs, and kick the graph sideways on plateaus.
    if d >= 3 and D >= 2:
        try:
            budget = 0.88 * time_limit - (time.monotonic() - start) - 2.0
            if budget >= 1.0:
                out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
