import itertools
import math
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

#define MAXN 2048
#define MAXD 48
#define WMAX (MAXN / 64)
#define ANN_IT 250
#define STALL_MAX 60

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} state_t;

static int d_, D_;
static int N, words;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t bufA[MAXN][WMAX], bufB[MAXN][WMAX];
static uint64_t ballD[MAXN][WMAX], ballR[MAXN][WMAX];
static state_t snap_s, best_s;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int j = 0; j < deg[u]; j++) if (adj[u][j] == v) return 1;
    return 0;
}

static void rem_arc(int u, int v) {
    for (int j = 0; j < deg[u]; j++) {
        if (adj[u][j] == v) { adj[u][j] = adj[u][--deg[u]]; return; }
    }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) { rem_arc(u, v); rem_arc(v, u); }

/* out[v] = bitmask of vertices within distance r of v. */
static void compute_ball(int r, uint64_t out[][WMAX]) {
    int W = words;
    uint64_t (*cu)[WMAX] = bufA, (*nx)[WMAX] = bufB;
    uint64_t (*tp)[WMAX];
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < W; k++) cu[v][k] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < W; k++) nx[v][k] = cu[v][k];
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v][j];
                for (int k = 0; k < W; k++) nx[v][k] |= cu[u][k];
            }
        }
        tp = cu; cu = nx; nx = tp;
    }
    for (int v = 0; v < N; v++) for (int k = 0; k < W; k++) out[v][k] = cu[v][k];
}

/* Number of unordered pairs at distance > D_. */
static long cost(void) {
    compute_ball(D_, ballD);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < words; k++) c += pop64(ballD[v][k]);
        bad += N - c;
    }
    return bad / 2;
}

/* Add a vertex on side 1-c joined to a greedy cover (radius D_-1) of side c. */
static int try_add(int c) {
    int Nold = N, W = words;
    compute_ball(D_ - 1, ballR);
    static uint64_t cov[WMAX];
    static int cand[MAXN];
    int nc = 0, chosen[MAXD], nch = 0, covc = 0;
    memset(cov, 0, sizeof cov);
    for (int v = 0; v < Nold; v++) if (col[v] == c && deg[v] < d_) cand[nc++] = v;
    while (covc < Nold && nch < d_ && nc > 0) {
        int bi = -1;
        long bkey = -1;
        for (int i = 0; i < nc; i++) {
            int s = cand[i], g = 0;
            for (int k = 0; k < W; k++) g += pop64(ballR[s][k] & ~cov[k]);
            if (g == 0) continue;
            long key = (long)g * 8 + rint_(8);
            if (key > bkey) { bkey = key; bi = i; }
        }
        if (bi < 0) break;
        int s = cand[bi];
        cand[bi] = cand[--nc];
        chosen[nch++] = s;
        covc = 0;
        for (int k = 0; k < W; k++) { cov[k] |= ballR[s][k]; covc += pop64(cov[k]); }
    }
    if (covc < Nold) return 0;
    int v = Nold;
    N = Nold + 1;
    words = (N + 63) / 64;
    deg[v] = 0;
    col[v] = 1 - c;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], v);
    return 1;
}

/* Join deficient opposite-side pairs (only shortens distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d_) { if (col[v] == 0) L[nl++] = v; else R[nr++] = v; }
    }
    for (int i = nl - 1; i > 0; i--) { int j = rint_(i + 1); int t = L[i]; L[i] = L[j]; L[j] = t; }
    for (int i = nr - 1; i > 0; i--) { int j = rint_(i + 1); int t = R[i]; R[i] = R[j]; R[j] = t; }
    for (int i = 0; i < nl; i++) {
        for (int j = 0; j < nr; j++) {
            int a = L[i], b = R[j];
            if (deg[a] < d_ && deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. True if cost reaches 0. */
static int anneal(int iters) {
    static int S0[MAXN];
    int n0 = 0;
    for (int v = 0; v < N; v++) if (col[v] == 0 && deg[v] > 0) S0[n0++] = v;
    long cur = cost();
    if (n0 < 2) return cur == 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 15 && now() > t_end) break;
        int a = S0[rint_(n0)], c = S0[rint_(n0)];
        if (a == c) continue;
        int b = adj[a][rint_(deg[a])];
        int e = adj[c][rint_(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b); del_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long nw = cost();
        int acc = nw <= cur;
        if (!acc) {
            double T = 0.5 * (1.0 - (double)it / iters) + 0.02;
            acc = rdbl() < exp(-(double)(nw - cur) / T);
        }
        if (acc) cur = nw;
        else { del_edge(a, e); del_edge(c, b); add_edge(a, b); add_edge(c, e); }
    }
    return cur == 0;
}

static void remove_vertex(int v) {
    for (int j = 0; j < deg[v]; j++) rem_arc(adj[v][j], v);
    deg[v] = 0;
    int last = N - 1;
    if (v != last) {
        for (int j = 0; j < deg[last]; j++) {
            int u = adj[last][j];
            for (int t = 0; t < deg[u]; t++) if (adj[u][t] == last) { adj[u][t] = v; break; }
        }
        memcpy(adj[v], adj[last], sizeof(int) * deg[last]);
        deg[v] = deg[last];
        col[v] = col[last];
    }
    deg[last] = 0;
    N--;
    words = (N + 63) / 64;
}

static void kill_random(int k) {
    for (int t = 0; t < k && N > 3; t++) remove_vertex(rint_(N));
}

/* Add a non-adjacent twin of a vertex whose neighbours have spare degree. Keeps validity. */
static int try_twin(void) {
    if (N >= MAXN - 1) return 0;
    for (int t = 0; t < 40; t++) {
        int v = rint_(N);
        if (deg[v] == 0) continue;
        int ok = 1;
        for (int j = 0; j < deg[v]; j++) if (deg[adj[v][j]] >= d_) { ok = 0; break; }
        if (!ok) continue;
        int w = N;
        N++;
        words = (N + 63) / 64;
        deg[w] = 0;
        col[w] = col[v];
        for (int j = 0; j < deg[v]; j++) {
            int u = adj[v][j];
            adj[w][deg[w]++] = u;
            adj[u][deg[u]++] = w;
        }
        return 1;
    }
    return 0;
}

static void twin_grow(void) {
    int fails = 0;
    while (fails < 25) {
        if (try_twin()) fails = 0;
        else fails++;
    }
}

static void save_to(state_t *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof(int) * N);
    memcpy(s->col, col, sizeof(int) * N);
    for (int v = 0; v < N; v++) memcpy(s->adj[v], adj[v], sizeof(int) * deg[v]);
}

static void load_from(const state_t *s) {
    N = s->n;
    words = (N + 63) / 64;
    memcpy(deg, s->deg, sizeof(int) * N);
    memcpy(col, s->col, sizeof(int) * N);
    for (int v = 0; v < N; v++) memcpy(adj[v], s->adj[v], sizeof(int) * deg[v]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double budget = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 2) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 64 || m < 0) { printf("0 0\n"); return 0; }
    N = n;
    words = (N + 63) / 64;
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    static int stk[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int j = 0; j < deg[u]; j++) {
                int v = adj[u][j];
                if (col[v] == -1) { col[v] = 1 - col[u]; stk[sp++] = v; }
                else if (col[v] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    t_end = now() + budget;
    if (cost() != 0) { printf("0 0\n"); return 0; }
    save_to(&best_s);
    twin_grow();
    if (N > best_s.n) save_to(&best_s);

    int stall = 0;
    while (now() < t_end) {
        int r = rint_(10);
        if (r == 0) {
            twin_grow();
        } else {
            save_to(&snap_s);
            int ok;
            if (r < 7) {
                ok = try_add(rint_(2));
                if (ok) { fill(); ok = anneal(ANN_IT); }
            } else {
                kill_random(1 + rint_(3));
                fill();
                ok = anneal(ANN_IT);
            }
            if (!ok) { load_from(&snap_s); stall++; }
            else stall = 0;
        }
        if (N > best_s.n) { save_to(&best_s); stall = 0; }
        if (N + 3 < best_s.n || stall > STALL_MAX) { load_from(&best_s); stall = 0; }
    }

    long E = 0;
    for (int v = 0; v < best_s.n; v++) E += best_s.deg[v];
    printf("%d %ld\n", best_s.n, E / 2);
    for (int v = 0; v < best_s.n; v++) {
        for (int j = 0; j < best_s.deg[v]; j++) {
            int u = best_s.adj[v][j];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
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
# Voltage lifts over small (cyclic or semidirect) groups.
# ----------------------------------------------------------------------------

def _pick_group(order, rng):
    """Return (order, mul) for a cyclic or a semidirect group of the given order."""
    if order >= 4 and rng.random() < 0.5:
        ks = [k for k in range(2, 13) if order % k == 0 and order // k >= 2]
        rng.shuffle(ks)
        for k in ks:
            m = order // k
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                r = rng.choice(rs)
                try:
                    o, mul, _ = lib.semidirect_group(m, k, r)
                    return o, mul
                except ValueError:
                    continue
    o, mul, _ = lib.cyclic_group(order)
    return o, mul


def _init_darts(s, d, order, rng):
    """Darts (u, v, g): A vertex u, B vertex v (local indices), voltage g. Each vertex gets d darts."""
    slots = [v for v in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    seen = set()
    for u in range(s):
        for j in range(d):
            v = slots[u * d + j]
            for _ in range(60):
                g = rng.randrange(order)
                if (u, v, g) not in seen:
                    break
            else:
                return None
            seen.add((u, v, g))
            darts.append((u, v, g))
    return darts


def _lift(s, darts, order, mul):
    """Lift the base graph: A side is 0..s-1, B side is s..2s-1 in the base."""
    return lib.group_lift(2 * s, [(u, s + v, g) for u, v, g in darts], order, mul)


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Hill-climb voltages of random bipartite base lifts until a diameter-D lift appears."""
    base_pick = (1, 1, 2, 2, 3)
    while time.monotonic() < deadline:
        s = rng.choice(base_pick)
        base_n = 2 * s
        lo = best_n // base_n
        order = lo + 1 + rng.randrange(0, max(2, lo // 8 + 1))
        order, mul = _pick_group(order, rng)
        darts = _init_darts(s, d, order, rng)
        if darts is None:
            continue
        n, e = _lift(s, darts, order, mul)
        cost = lib.bad_pairs(n, e, D)
        steps = 0
        while cost > 0 and steps < 250 and time.monotonic() < deadline:
            steps += 1
            i = rng.randrange(len(darts))
            u, v, old = darts[i]
            g2 = rng.randrange(order)
            if g2 == old or (u, v, g2) in set(darts):
                continue
            darts[i] = (u, v, g2)
            n2, e2 = _lift(s, darts, order, mul)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost or rng.random() < 0.02:
                cost, n, e = c2, n2, e2
            else:
                darts[i] = (u, v, old)
        if cost == 0 and time.monotonic() < deadline:
            if n > best_n and lib.is_valid(n, e, d, D):
                consider(n, e)
                best_n = max(best_n, n)
            n3, e3 = _grow(n, e, d, D, deadline, rng)
            consider(n3, e3)
            best_n = max(best_n, n3)


# ----------------------------------------------------------------------------
# Driver. Python builds structured and lifted bases; the C engine (annealed
# kill / repair / regrow search with twin growth) then runs on the best graph.
# Every candidate passes lib.is_valid before it is kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end_all = start + 0.90 * time_limit
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured base, grown by covers and saturation.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            if lib.is_valid(n0, e0, d, D):
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
                consider(n1, e1)

    # Phase B: randomized twin / grow / saturate trials.
    if D >= 2:
        trial_end = at(0.14)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and d >= 2:
        _lift_search(d, D, best_n, rng, at(0.30), consider)

    # Phase C: C annealing search from the best valid graph.
    if D >= 2 and d <= 40 and best_n <= 1500 and best_n < lib.moore_bound(d, D):
        budget = end_all - time.monotonic() - 1.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=max(1.0, start + 0.95 * time_limit - time.monotonic()))
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
