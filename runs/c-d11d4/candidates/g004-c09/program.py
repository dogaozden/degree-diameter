"""Search program for bipartite graphs with max degree d and diameter D.

New in this version:
- C engine: cover-seeded vertex insertion. A new vertex's neighbours are chosen
  greedily so their radius-(D-1) balls cover every existing vertex. The uncovered
  count is then the exact number of bad pairs created by the insertion.
- C engine: simulated annealing repair with degree-preserving moves (double-edge
  switches), endpoint moves and edge additions. Bipartiteness and degree bounds
  are preserved by construction, so only the diameter cost is evaluated. Cost is
  the number of pairs at distance > D, computed with bitsets.
- Python: the generalized quadrangle W(q) start for D >= 4 is grown by the
  twin/cover pipeline, then handed to the C engine for the rest of the budget.
  Every returned graph is checked with lib.is_valid, and K_{d,d} is the fallback.
"""
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

#define MAXN 4200
#define MAXD 40
#define MAXW ((MAXN + 63) / 64)
#define MAXE (MAXN * MAXD / 2 + 64)
#define STAGE_STEPS 1500

static int DEG_MAX, DIAM, N;
static int side[MAXN], deg[MAXN], nb[MAXN][MAXD];
static uint64_t bufA[MAXN * MAXW], bufB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double t_end;
static int snapN, snapM, snapSide[MAXN], snapE[MAXE][2];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}
static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) {
            int last = --deg[a];
            nb[a][i] = nb[a][last];
            return;
        }
    }
}
static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}
static void del_edge(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

/* Bitset balls of radius R around every vertex. Returns the buffer holding them. */
static uint64_t *compute_ball(int R) {
    int n = N, W = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s2 = cur + (size_t)nb[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long bad_pairs(void) {
    int n = N, W = (n + 63) / 64;
    uint64_t *b = compute_ball(DIAM);
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = b + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        tot += n - c;
    }
    return tot / 2;
}

/* Greedy cover: pick up to DEG_MAX vertices on the side opposite s whose balls
   (given in ball, radius DIAM-1 of the current graph) cover all current vertices. */
static int greedy_cover(const uint64_t *ball, int s, int *chosen, int *uncovered) {
    int n = N, W = (n + 63) / 64;
    uint64_t cov[MAXW], full[MAXW];
    memset(cov, 0, sizeof cov);
    memset(full, 0, sizeof full);
    for (int v = 0; v < n; v++) full[v >> 6] |= 1ULL << (v & 63);
    int nch = 0;
    while (nch < DEG_MAX) {
        int bestc = -1, bestg = 0, ties = 0;
        for (int c = 0; c < n; c++) {
            if (side[c] == s || deg[c] >= DEG_MAX) continue;
            const uint64_t *bc = ball + (size_t)c * W;
            int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(bc[w] & ~cov[w]);
            if (g > bestg) { bestg = g; bestc = c; ties = 1; }
            else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) bestc = c;
            }
        }
        if (bestc < 0) break;
        chosen[nch++] = bestc;
        const uint64_t *bb = ball + (size_t)bestc * W;
        for (int w = 0; w < W; w++) cov[w] |= bb[w];
    }
    int unc = 0;
    for (int w = 0; w < W; w++) unc += __builtin_popcountll(full[w] & ~cov[w]);
    *uncovered = unc;
    return nch;
}

/* Insert one new vertex on whichever side gives the smaller uncovered count. */
static void add_vertex(void) {
    if (N + 2 >= MAXN) return;
    uint64_t *ball = compute_ball(DIAM - 1);
    int ch[2][MAXD], k[2], unc[2];
    for (int s = 0; s < 2; s++) k[s] = greedy_cover(ball, s, ch[s], &unc[s]);
    int s;
    if (unc[0] < unc[1]) s = 0;
    else if (unc[1] < unc[0]) s = 1;
    else s = rndint(2);
    int v = N++;
    side[v] = s;
    deg[v] = 0;
    for (int i = 0; i < k[s]; i++) add_edge(v, ch[s][i]);
}

/* Random vertex on side s (or any side if s < 0) satisfying the requested conditions. */
static int pick(int s, int need_spare, int need_deg) {
    for (int t = 0; t < 64; t++) {
        int v = rndint(N);
        if (s >= 0 && side[v] != s) continue;
        if (need_spare && deg[v] >= DEG_MAX) continue;
        if (need_deg && deg[v] == 0) continue;
        return v;
    }
    return -1;
}

typedef struct { int type, a, b, c, e; } Move;

/* type 0: double switch (a,b),(c,e) -> (a,e),(c,b), with a,c on side 0.
   type 1: endpoint move (a,b) -> (a,c), c on the side of b.
   type 2: add edge (a,b). */
static int propose(Move *mv) {
    int r = rndint(100);
    if (r < 50) {
        int a = pick(0, 0, 1), c = pick(0, 0, 1);
        if (a < 0 || c < 0 || a == c) return 0;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
        mv->type = 0; mv->a = a; mv->b = b; mv->c = c; mv->e = e;
        return 1;
    }
    if (r < 92) {
        int x = pick(-1, 0, 1);
        if (x < 0) return 0;
        int y = nb[x][rndint(deg[x])];
        int z = pick(side[y], 1, 0);
        if (z < 0 || z == y || has_edge(x, z)) return 0;
        mv->type = 1; mv->a = x; mv->b = y; mv->c = z; mv->e = -1;
        return 1;
    }
    int x = pick(0, 1, 0), z = pick(1, 1, 0);
    if (x < 0 || z < 0 || has_edge(x, z)) return 0;
    mv->type = 2; mv->a = x; mv->b = z; mv->c = -1; mv->e = -1;
    return 1;
}

static void apply_move(const Move *m) {
    if (m->type == 0) {
        del_edge(m->a, m->b); del_edge(m->c, m->e);
        add_edge(m->a, m->e); add_edge(m->c, m->b);
    } else if (m->type == 1) {
        del_edge(m->a, m->b); add_edge(m->a, m->c);
    } else {
        add_edge(m->a, m->b);
    }
}

static void undo_move(const Move *m) {
    if (m->type == 0) {
        del_edge(m->a, m->e); del_edge(m->c, m->b);
        add_edge(m->a, m->b); add_edge(m->c, m->e);
    } else if (m->type == 1) {
        del_edge(m->a, m->c); add_edge(m->a, m->b);
    } else {
        del_edge(m->a, m->b);
    }
}

/* Metropolis search on the bad-pair count. Returns 1 if cost reached 0. */
static int anneal(long long cur, int steps) {
    double T = 1.5, Tmin = 0.2;
    double decay = pow(Tmin / 1.5, 1.0 / (double)steps);
    Move mv;
    for (int s = 0; s < steps && cur > 0; s++, T *= decay) {
        if (now_s() >= t_end) break;
        if (!propose(&mv)) continue;
        apply_move(&mv);
        long long c2 = bad_pairs();
        long long dl = c2 - cur;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) cur = c2;
        else undo_move(&mv);
    }
    return cur == 0;
}

static void save_snap(void) {
    snapN = N;
    memcpy(snapSide, side, sizeof(int) * (size_t)N);
    snapM = 0;
    for (int a = 0; a < N; a++)
        for (int i = 0; i < deg[a]; i++) {
            int b = nb[a][i];
            if (a < b) {
                snapE[snapM][0] = a;
                snapE[snapM][1] = b;
                snapM++;
            }
        }
}

static void load_snap(void) {
    N = snapN;
    memcpy(side, snapSide, sizeof(int) * (size_t)N);
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < snapM; i++) add_edge(snapE[i][0], snapE[i][1]);
}

static int colorize(void) {
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int w = nb[u][i];
                if (side[w] < 0) {
                    side[w] = 1 - side[u];
                    q[tail++] = w;
                } else if (side[w] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    DEG_MAX = d;
    DIAM = D;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (d < 1 || d > MAXD - 1 || D < 2 || n < 1 || n > MAXN - 4 || m < 0 || m > MAXE) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || has_edge(u, v) ||
            deg[u] >= d || deg[v] >= d) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }
    if (!colorize()) { printf("0 0\n"); return 0; }

    t_end = budget;
    int have = 0;
    long long c0 = bad_pairs();
    if (c0 == 0) {
        save_snap();
        have = 1;
    } else if (anneal(c0, STAGE_STEPS)) {
        save_snap();
        have = 1;
    }

    while (have && now_s() < t_end) {
        if (snapN + 4 >= MAXN) break;
        load_snap();
        add_vertex();
        long long cur = bad_pairs();
        if (cur == 0 || anneal(cur, STAGE_STEPS)) save_snap();
    }

    if (!have) { printf("0 0\n"); return 0; }
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapE[i][0], snapE[i][1]);
    return 0;
}
"""


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
# Twin extension (Python pipeline, used to build the start graph).
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices."""
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


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    """Plateau-walking swap search for a cover of `full` by at most d candidates."""
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
    return None


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
            if not chosen and time.monotonic() < deadline:
                chosen = _local_cover(cands, ball, full, d, rng, 400, deadline)
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
    """Extend by cover vertices FIRST, then saturate edges with the remaining spare degree."""
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families (D = 3 and fallback).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Orchestration.
# ----------------------------------------------------------------------------

def _offer(st, n, e, d, D):
    """Keep (n, e) as the best graph if it is larger and valid."""
    if n > st["best"][0] and lib.is_valid(n, e, d, D):
        st["best"] = (n, list(e))


def _gq_stage(st, gq, d, D, rng, end):
    """Grow the generalized quadrangle start with the Python twin/cover pipeline."""
    _offer(st, gq[0], gq[1], d, D)
    for _ in range(8):
        if time.monotonic() >= end:
            break
        pn, pe = _pipeline(gq[0], gq[1], d, D, end, rng)
        _offer(st, pn, pe, d, D)


def _c_stage(st, d, D, seed, start, time_limit):
    """Hand the current best graph to the C engine for the rest of the time budget."""
    if st["best"][0] >= lib.moore_bound(d, D):
        return
    budget = start + 0.85 * time_limit - time.monotonic() - 1.0
    if budget < 2.0:
        return
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=st["best"], timeout=budget + 5.0)
        n, e = lib.parse_graph_text(text)
        _offer(st, n, e, d, D)
    except Exception:
        pass


def _parent_search(st, d, D, rng, start, time_limit):
    """Projective-plane pipelines and Python lift searches (D = 3 and fallback cases)."""
    deadline = start + 0.85 * time_limit
    ext_deadline = start + 0.5 * time_limit

    def consider(n, e):
        _offer(st, n, e, d, D)

    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        best_n = st["best"][0]
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            gs = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(gs["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                gs["G"] = G + gs["step"]
                gs["step"] = min(gs["step"] * 2, max(1, G // 10))
                gs["miss"] = 0
            else:
                gs["G"] = G
                gs["miss"] += 1
                if gs["miss"] >= 3:
                    gs["step"] = 1
                    gs["miss"] = 0
                    gs["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    st = {"best": lib.haar_graph(d, range(d))}

    gq = _best_gq(d) if D >= 4 else None
    if gq is not None:
        # Generalized quadrangle start, then the C annealing/insertion engine.
        _gq_stage(st, gq, d, D, rng, start + 0.25 * time_limit)
        _c_stage(st, d, D, seed, start, time_limit)
    else:
        _parent_search(st, d, D, rng, start, time_limit)

    best = st["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
