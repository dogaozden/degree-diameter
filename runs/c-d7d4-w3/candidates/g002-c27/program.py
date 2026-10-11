import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(10000)


# ----------------------------------------------------------------------------
# C engine: incremental vertex insertion with bipartite annealing.
#
# Idea: keep a valid bipartite graph (diameter <= D, degree <= d). Insert one
# new vertex on a random side, joined to d opposite-side vertices (evicting one
# edge at a full vertex if needed). This creates bad pairs. Then anneal with
# degree-preserving bipartite double-edge switches and free edge-fills, with the
# cost = number of vertex pairs at distance > D (bitset BFS, radius D).
# Success (cost 0) makes a larger valid graph, which becomes the new base.
# Failure restores the base and retries with fresh randomness.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXW (MAXN / 64)
#define MAXD 64

static int N, Dd, DIAM;
static int deg[MAXN];
static int col[MAXN];
static int adjv[MAXN][MAXD];

static int sN;
static int sdeg[MAXN];
static int scol[MAXN];
static int sadj[MAXN][MAXD];

static uint64_t BA[MAXN][MAXW];
static uint64_t BB[MAXN][MAXW];

static uint64_t rs = 88172645463325252ULL;
static double t_end;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    int i;
    for (i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counts). */
static long long cost_fn(void) {
    int W = (N + 63) >> 6;
    int r, v, i, w;
    for (v = 0; v < N; v++) {
        for (w = 0; w < W; w++) BA[v][w] = 0;
        BA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            for (w = 0; w < W; w++) BB[v][w] = BA[v][w];
            for (i = 0; i < deg[v]; i++) {
                int u = adjv[v][i];
                for (w = 0; w < W; w++) BB[v][w] |= BA[u][w];
            }
        }
        for (v = 0; v < N; v++)
            for (w = 0; w < W; w++) BA[v][w] = BB[v][w];
    }
    long long bad = 0;
    for (v = 0; v < N; v++) {
        int c = 0;
        for (w = 0; w < W; w++) c += pc64(BA[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static void save_state(void) {
    int v, j;
    sN = N;
    for (v = 0; v < N; v++) {
        sdeg[v] = deg[v];
        scol[v] = col[v];
        for (j = 0; j < deg[v]; j++) sadj[v][j] = adjv[v][j];
    }
}

static void load_state(void) {
    int v, j;
    N = sN;
    for (v = 0; v < N; v++) {
        deg[v] = sdeg[v];
        col[v] = scol[v];
        for (j = 0; j < deg[v]; j++) adjv[v][j] = sadj[v][j];
    }
}

/* Insert a new vertex on a random side; prefer spare-degree partners,
   then evict one edge at a full partner. */
static void add_vertex(void) {
    int c = rndint(2);
    int v = N;
    int chosen = 0, tries = 0;
    N++;
    col[v] = c;
    deg[v] = 0;
    while (chosen < Dd && tries < 200 * N) {
        int u;
        tries++;
        u = rndint(N - 1);
        if (col[u] == c || has_edge(v, u)) continue;
        if (deg[u] >= Dd) {
            int w;
            if (tries < 20 * N) continue;
            w = adjv[u][rndint(deg[u])];
            del_edge(u, w);
        }
        add_edge(v, u);
        chosen++;
    }
}

/* Simulated annealing over degree-preserving bipartite switches and
   free edge fills. Returns final cost (0 means a valid graph). */
static long long anneal(long long cur, int iters) {
    int it;
    for (it = 0; it < iters && cur > 0; it++) {
        double T;
        if ((it & 63) == 0 && now() > t_end) break;
        T = 0.05 + 0.6 * (1.0 - (double)it / (double)iters);
        if (rnd01() < 0.15) {
            int a = -1, b = -1, t;
            for (t = 0; t < 30; t++) {
                int x = rndint(N), y = rndint(N);
                if (col[x] == 0 && col[y] == 1 && deg[x] < Dd && deg[y] < Dd && !has_edge(x, y)) {
                    a = x;
                    b = y;
                    break;
                }
            }
            if (a >= 0) {
                add_edge(a, b);
                cur = cost_fn();
            }
            continue;
        }
        {
            int a = rndint(N), c = rndint(N), b, e;
            long long nw;
            if (a == c || col[a] != 0 || col[c] != 0 || deg[a] == 0 || deg[c] == 0) continue;
            b = adjv[a][rndint(deg[a])];
            e = adjv[c][rndint(deg[c])];
            if (has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            nw = cost_fn();
            if (nw <= cur || rnd01() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    int n, m, i, bad = 0;
    double limit;
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 20; i++) rnd64();
    limit = atof(argv[4]);
    t_end = now() + limit;

    if (Dd < 2 || Dd >= MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n < 1 || n > MAXN - 2 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (i = 0; i < N; i++) {
        deg[i] = 0;
        col[i] = -1;
    }
    for (i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { bad = 1; break; }
        if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) { bad = 1; break; }
        add_edge(u, v);
    }
    if (!bad) {
        int *stack = (int *)malloc(sizeof(int) * (N + 1));
        for (i = 0; i < N && !bad; i++) {
            int top = 0;
            if (col[i] != -1) continue;
            col[i] = 0;
            stack[top++] = i;
            while (top > 0 && !bad) {
                int x = stack[--top];
                int j;
                for (j = 0; j < deg[x]; j++) {
                    int y = adjv[x][j];
                    if (col[y] == -1) {
                        col[y] = 1 - col[x];
                        stack[top++] = y;
                    } else if (col[y] == col[x]) {
                        bad = 1;
                        break;
                    }
                }
            }
        }
        free(stack);
    }
    if (bad || cost_fn() != 0) {
        printf("0 0\n");
        return 0;
    }

    save_state();
    while (now() < t_end && sN < MAXN - 2) {
        long long c;
        load_state();
        add_vertex();
        c = cost_fn();
        c = anneal(c, 2500);
        if (c == 0) save_state();
    }

    load_state();
    {
        int v, j, M = 0;
        for (v = 0; v < N; v++)
            for (j = 0; j < deg[v]; j++)
                if (adjv[v][j] > v) M++;
        printf("%d %d\n", N, M);
        for (v = 0; v < N; v++)
            for (j = 0; j < deg[v]; j++)
                if (adjv[v][j] > v) printf("%d %d\n", v, adjv[v][j]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d (q = smallest prime power >= d)."""
    q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _perfect_matching(n, adj, color, rng):
    """Random perfect matching of the bipartite graph (Kuhn augmentation). dict left->right, or None."""
    left = [v for v in range(n) if color[v] == 0]
    nb = {}
    for u in left:
        lst = list(adj[u])
        rng.shuffle(lst)
        nb[u] = lst
    match_l = {}
    match_r = {}
    for u in left:
        for v in nb[u]:
            if v not in match_r:
                match_l[u] = v
                match_r[v] = u
                break

    def augment(u, seen):
        for v in nb[u]:
            if v in seen:
                continue
            seen.add(v)
            w = match_r.get(v)
            if w is None or augment(w, seen):
                match_l[u] = v
                match_r[v] = u
                return True
        return False

    for u in left:
        if u not in match_l:
            if not augment(u, set()):
                return None
    if len(match_l) != len(left):
        return None
    return match_l


def _regular_thin(n, edges, d, rng):
    """For a (d+1)-regular bipartite graph, drop a random perfect matching. Returns edges or None."""
    adj = _to_sets(n, edges)
    if any(len(a) != d + 1 for a in adj):
        return None
    color = _bipartition(n, adj)
    match = _perfect_matching(n, adj, color, rng)
    if match is None:
        return None
    drop = {(min(u, v), max(u, v)) for u, v in match.items()}
    return [(u, v) for u, v in edges if (min(u, v), max(u, v)) not in drop]


def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = None
    if rng.random() < 0.8:
        e = _regular_thin(raw_n, raw_e, d, rng)
    if e is None:
        e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

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


def _local_kill(n, edges, k, rng):
    """Vertex set of size <= k grown by BFS from a random vertex (a local 'wound')."""
    adj = _to_sets(n, edges)
    s = rng.randrange(n)
    seen = [s]
    seen_set = {s}
    i = 0
    while len(seen) < k and i < len(seen):
        nbrs = list(adj[seen[i]])
        rng.shuffle(nbrs)
        for u in nbrs:
            if len(seen) >= k:
                break
            if u not in seen_set:
                seen_set.add(u)
                seen.append(u)
        i += 1
    return seen_set


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4, 6))
        if k >= cur_n:
            break
        if rng.random() < 0.5:
            kill = set(rng.sample(range(cur_n), k))
        else:
            kill = _local_kill(cur_n, cur_e, k, rng)
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials, Python LNS
#   B  thinned dense graph (regular matching thinning or degree reduction + deletion)
#   C  C engine: vertex insertion + bipartite annealing from the best valid graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.88 * time_limit

    def at(f):
        return start + f * total

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

    # Phase A: structured small base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.14)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.22), rng, consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.30):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.30):
                r = _deletion_trial(d, D, rn, re, rng, at(0.30))
                if r is None:
                    break
                consider(*r)

    # Phase C: C engine insertion + annealing from the best valid graph.
    # Skipped when the Moore bound is already reached (e.g. the calibration case).
    if D >= 2 and time_limit >= 8 and best_n < lib.moore_bound(d, D):
        budget = start + total - time.monotonic() - 1.0
        if budget >= 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=(best_n, list(best_e)),
                                 timeout=budget + 10.0)
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
