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

#define MAXN 2048
#define MAXW 32
#define MAXD 32

typedef struct {
    int n;
    int deg[MAXN];
    int side[MAXN];
    int adj[MAXN][MAXD];
} State;

static State G, B, S;
static int d, D;
static double tlimit;
static uint64_t rs = 88172645463325252ULL;
static uint64_t ball[MAXN][MAXW];
static uint64_t tmpb[MAXN][MAXW];
static int s0[MAXN];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int m) { return (int)(rnd() % (uint64_t)m); }

static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < G.deg[a]; i++)
        if (G.adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}

static void drop_from(int x, int y) {
    for (int i = 0; i < G.deg[x]; i++) {
        if (G.adj[x][i] == y) {
            G.adj[x][i] = G.adj[x][G.deg[x] - 1];
            G.deg[x]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    drop_from(a, b);
    drop_from(b, a);
}

static void set_nb(int x, int old, int nw) {
    for (int i = 0; i < G.deg[x]; i++) {
        if (G.adj[x][i] == old) {
            G.adj[x][i] = nw;
            return;
        }
    }
}

/* Double-edge switch: a-b, c-e become a-e, c-b. Degrees unchanged. */
static void switch_(int a, int b, int c, int e) {
    set_nb(a, b, e);
    set_nb(b, a, c);
    set_nb(c, e, b);
    set_nb(e, c, a);
}

/* ball[v] = bitset of vertices within distance r of v. */
static void compute_balls(int r, uint64_t (*out)[MAXW]) {
    int n = G.n, W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) out[v][w] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) tmpb[v][w] = out[v][w];
            for (int i = 0; i < G.deg[v]; i++) {
                int u = G.adj[v][i];
                for (int w = 0; w < W; w++) tmpb[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmpb[v][w];
    }
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long long cost_full(void) {
    int n = G.n, W = (n + 63) >> 6;
    compute_balls(D, ball);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(ball[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add cross-side edges between deficient vertices. Only shortens distances. */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < G.n; v++) {
        if (G.deg[v] >= d) continue;
        if (G.side[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rint_(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && G.deg[a] < d; j++) {
            int b = R[j];
            if (G.deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int pick_s0(int m) {
    for (int t = 0; t < 8; t++) {
        int a = s0[rint_(m)];
        if (G.deg[a] > 0) return a;
    }
    return -1;
}

/* Simulated annealing over bipartite switches minimising bad pairs. Returns 1 if valid. */
static int anneal(int iters, double T0, double T1) {
    long long cur = cost_full();
    if (cur == 0) return 1;
    int m = 0;
    for (int v = 0; v < G.n; v++)
        if (G.side[v] == 0) s0[m++] = v;
    if (m < 2) return 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > tlimit) break;
        double T = T0 + (T1 - T0) * (double)it / (double)iters;
        int a = pick_s0(m), c = pick_s0(m);
        if (a < 0 || c < 0 || a == c) continue;
        int b = G.adj[a][rint_(G.deg[a])];
        int e = G.adj[c][rint_(G.deg[c])];
        if (b == e) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        switch_(a, b, c, e);
        long long nw = cost_full();
        if (nw <= cur || rdbl() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            switch_(a, e, c, b);
        }
    }
    return cur == 0;
}

/* Add one vertex attached to a greedy cover of the other side, then repair. */
static int grow_attempt(int iters) {
    if (D < 2 || G.n + 2 >= MAXN) return 0;
    int n = G.n, W = (n + 63) >> 6;
    compute_balls(D - 1, ball);
    int s = rint_(2);
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    static char used[MAXN];
    for (int x = 0; x < n; x++) used[x] = 0;
    int chosen[MAXD];
    int nch = 0;
    for (int k = 0; k < d && k < MAXD; k++) {
        int bx = -1;
        double bs = -1e18;
        for (int x = 0; x < n; x++) {
            if (G.side[x] != s || used[x]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(ball[x][w] & ~cov[w]);
            double sc = g - (G.deg[x] >= d ? 0.75 : 0.0) + 0.3 * rdbl();
            if (sc > bs) {
                bs = sc;
                bx = x;
            }
        }
        if (bx < 0) break;
        used[bx] = 1;
        chosen[nch++] = bx;
        for (int w = 0; w < W; w++) cov[w] |= ball[bx][w];
    }
    if (nch == 0) return 0;
    int v = G.n++;
    G.side[v] = 1 - s;
    G.deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int x = chosen[i];
        if (G.deg[x] >= d) {
            int y = G.adj[x][rint_(G.deg[x])];
            remove_edge(x, y);
        }
        add_edge(x, v);
    }
    fill();
    return anneal(iters, 0.8, 0.05);
}

/* Delete vertex k; the last vertex is moved into slot k to keep labels 0..n-1. */
static void remove_vertex(int k) {
    for (int i = 0; i < G.deg[k]; i++) drop_from(G.adj[k][i], k);
    G.deg[k] = 0;
    int L = G.n - 1;
    if (k != L) {
        for (int i = 0; i < G.deg[L]; i++) set_nb(G.adj[L][i], L, k);
        G.deg[k] = G.deg[L];
        for (int i = 0; i < G.deg[L]; i++) G.adj[k][i] = G.adj[L][i];
        G.side[k] = G.side[L];
    }
    G.deg[L] = 0;
    G.n--;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]);
    for (int i = 0; i < 10; i++) rnd();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    int ok = (n >= 1 && n < MAXN - 64 && d >= 1 && d < MAXD && m >= 0);
    if (!ok) { printf("0 0\n"); return 0; }

    memset(&G, 0, sizeof G);
    G.n = n;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (G.deg[u] >= d || G.deg[v] >= d) { ok = 0; break; }
        if (has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* 2-colour the graph; reject if not bipartite. */
    for (int v = 0; v < n; v++) G.side[v] = -1;
    static int stack[MAXN];
    for (int s = 0; s < n && ok; s++) {
        if (G.side[s] != -1) continue;
        G.side[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < G.deg[u]; i++) {
                int w = G.adj[u][i];
                if (G.side[w] == -1) {
                    G.side[w] = 1 - G.side[u];
                    stack[sp++] = w;
                } else if (G.side[w] == G.side[u]) {
                    ok = 0;
                    break;
                }
            }
            if (!ok) break;
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    B = G;
    int fails = 0;
    while (now() < tlimit) {
        if (G.n < B.n - 3 || fails > 60) {
            G = B;
            if (fails > 60) {
                int kills = 1 + rint_(2);
                for (int k = 0; k < kills && G.n > 2; k++) remove_vertex(rint_(G.n));
                fill();
                if (!anneal(3000, 0.8, 0.05)) G = B;
            }
            fails = 0;
            continue;
        }
        S = G;
        if (grow_attempt(3000)) {
            if (G.n > B.n) B = G;
            fails = 0;
        } else {
            G = S;
            fails++;
        }
    }

    int em = 0;
    for (int u = 0; u < B.n; u++)
        for (int i = 0; i < B.deg[u]; i++)
            if (B.adj[u][i] > u) em++;
    printf("%d %d\n", B.n, em);
    for (int u = 0; u < B.n; u++)
        for (int i = 0; i < B.deg[u]; i++)
            if (B.adj[u][i] > u) printf("%d %d\n", u, B.adj[u][i]);
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
    """W(q) incidence graph for the largest prime power q <= 9 with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Twin duplication and randomized pipelines.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
# Random voltage lifts with repair.
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


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Search random voltage lifts whose order is slightly above best_n, repair, then grow."""
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
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=30)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


# ----------------------------------------------------------------------------
# Python fallback: large-neighbourhood search, used only if the C engine fails.
# ----------------------------------------------------------------------------

def _add_vertex_py(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
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


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver.
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

    def at(frac):
        return start + frac * time_limit

    try:
        # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
        base_n, base_e = best_n, list(best_e)
        if D >= 3:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                n0, e0 = base
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.06), rng)
                consider(n1, e1)

        if D >= 2:
            trial_end = at(0.12)
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)
            _lift_search(d, D, at(0.2), rng, best_n, consider)
    except Exception:
        pass

    # Long C search from the best graph so far (kill, repair, regrow with annealing).
    if D >= 2 and d >= 2 and best_n < lib.moore_bound(d, D):
        c_ok = False
        budget = at(0.86) - 2.0 - time.monotonic()
        if budget > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
                c_ok = True
            except Exception:
                c_ok = False
        if not c_ok:
            try:
                _lns(best_n, best_e, d, D, at(0.85), rng, consider)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
