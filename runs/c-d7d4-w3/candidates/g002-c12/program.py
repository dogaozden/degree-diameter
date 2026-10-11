import itertools
import random
import sys
import time

import lib

sys.setrecursionlimit(10000)


# ----------------------------------------------------------------------------
# C engine: annealing over degree-preserving bipartite switches.
#
# State: bipartite graph with max degree d on N vertices. Cost = number of vertex
# pairs at distance > D (bitset balls). Moves are double-edge switches, random
# edge removals and greedy fills of deficient cross pairs. Every move is logged
# so a rejected move is undone exactly. When cost reaches 0 the graph is saved
# and a new vertex is inserted, displacing edges from saturated neighbours if
# needed. After a long stall the engine restores the best valid graph and
# perturbs it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 24
#define MAXLOG 16384
#define MAXE (MAXN * MAXD / 2)

static int Dd, DIAM, N;
static int deg[MAXN];
static int adjl[MAXN][MAXD];
static int side[MAXN];
static unsigned char amat[MAXN][MAXN];
static uint64_t bufA[MAXN][MAXW];
static uint64_t bufB[MAXN][MAXW];

static int bestN = -1;
static int bestDeg[MAXN], bestSide[MAXN];
static int bestAdj[MAXN][MAXD];

static int logT[MAXLOG], logA[MAXLOG], logB[MAXLOG];
static int logN = 0;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double t0;
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - t0; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_arr(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void list_remove(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adjl[a][k] == b) {
            adjl[a][k] = adjl[a][--deg[a]];
            return;
        }
    }
}

static void raw_add(int a, int b) {
    amat[a][b] = 1; amat[b][a] = 1;
    adjl[a][deg[a]++] = b;
    adjl[b][deg[b]++] = a;
}

static void raw_del(int a, int b) {
    amat[a][b] = 0; amat[b][a] = 0;
    list_remove(a, b);
    list_remove(b, a);
}

static void log_push(int t, int a, int b) {
    if (logN < MAXLOG) {
        logT[logN] = t; logA[logN] = a; logB[logN] = b;
        logN++;
    }
}

static void add_edge(int a, int b) { raw_add(a, b); log_push(1, a, b); }
static void del_edge(int a, int b) { raw_del(a, b); log_push(0, a, b); }

static void undo_log(void) {
    while (logN > 0) {
        logN--;
        if (logT[logN]) raw_del(logA[logN], logB[logN]);
        else raw_add(logA[logN], logB[logN]);
    }
}

static void reset_graph(void) {
    for (int i = 0; i < N; i++) memset(amat[i], 0, N);
    memset(deg, 0, sizeof deg);
    logN = 0;
    N = 0;
}

static void save_best(void) {
    bestN = N;
    for (int v = 0; v < N; v++) {
        bestDeg[v] = deg[v];
        bestSide[v] = side[v];
        for (int k = 0; k < deg[v]; k++) bestAdj[v][k] = adjl[v][k];
    }
}

static void restore_best(void) {
    int old = N;
    for (int i = 0; i < old; i++) memset(amat[i], 0, old);
    memset(deg, 0, sizeof deg);
    N = bestN;
    for (int v = 0; v < N; v++) {
        deg[v] = bestDeg[v];
        side[v] = bestSide[v];
        for (int k = 0; k < deg[v]; k++) adjl[v][k] = bestAdj[v][k];
    }
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) amat[v][adjl[v][k]] = 1;
    logN = 0;
}

/* Number of unordered pairs at distance > DIAM. */
static long cost_full(void) {
    int W = (N + 63) / 64;
    uint64_t (*cur)[MAXW] = bufA;
    uint64_t (*nxt)[MAXW] = bufB;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * MAXW);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                int u = adjl[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

static int pick_side(int s) {
    int v;
    do { v = rndi(N); } while (side[v] != s);
    return v;
}

/* Double-edge switch a-b, c-e  ->  a-e, c-b (a, c on side 0). Degrees unchanged. */
static int do_switch(void) {
    int a = pick_side(0), c = pick_side(0);
    if (a == c || deg[a] == 0 || deg[c] == 0) return 0;
    int b = adjl[a][rndi(deg[a])];
    int e = adjl[c][rndi(deg[c])];
    if (b == e) return 0;
    if (amat[a][e] || amat[c][b]) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

static void do_remove(void) {
    int a = rndi(N);
    if (deg[a] == 0) return;
    int b = adjl[a][rndi(deg[a])];
    del_edge(a, b);
}

/* Add cross-side edges between deficient vertices. Adding edges never raises cost. */
static void do_fill(int tries) {
    static int lst[2][MAXN];
    int cnt[2] = {0, 0};
    for (int v = 0; v < N; v++)
        if (deg[v] < Dd) lst[side[v]][cnt[side[v]]++] = v;
    if (cnt[0] == 0 || cnt[1] == 0) return;
    for (int t = 0; t < tries; t++) {
        int a = lst[0][rndi(cnt[0])];
        int b = lst[1][rndi(cnt[1])];
        if (deg[a] < Dd && deg[b] < Dd && !amat[a][b]) add_edge(a, b);
    }
}

/* Insert a vertex on a random side; take neighbours from deficient vertices first,
   then displace one random edge of saturated opposite-side vertices. Not logged. */
static void grow_one(void) {
    if (N >= MAXN - 2) return;
    int s = rndi(2);
    int v = N;
    N++;
    side[v] = s;
    deg[v] = 0;
    static int defi[MAXN], sat[MAXN];
    int nd = 0, ns = 0;
    for (int u = 0; u < v; u++) {
        if (side[u] == s) continue;
        if (deg[u] < Dd) defi[nd++] = u;
        else sat[ns++] = u;
    }
    shuffle_arr(defi, nd);
    shuffle_arr(sat, ns);
    int picked = 0;
    for (int i = 0; i < nd && picked < Dd; i++) {
        raw_add(v, defi[i]);
        picked++;
    }
    for (int i = 0; i < ns && picked < Dd; i++) {
        int u = sat[i];
        int w = adjl[u][rndi(deg[u])];
        raw_del(u, w);
        raw_add(v, u);
        picked++;
    }
}

static void make_kdd(void) {
    reset_graph();
    N = 2 * Dd;
    for (int i = 0; i < Dd; i++) {
        side[i] = 0;
        side[Dd + i] = 1;
    }
    for (int i = 0; i < Dd; i++)
        for (int j = 0; j < Dd; j++)
            raw_add(i, Dd + j);
}

static int load_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 1 || n > MAXN || m < 0 || m > MAXE) return 0;
    reset_graph();
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (amat[u][v] || deg[u] >= Dd || deg[v] >= Dd) return 0;
        raw_add(u, v);
    }
    static int queue[MAXN];
    for (int i = 0; i < n; i++) side[i] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int x = queue[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adjl[x][k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    queue[qt++] = y;
                } else if (side[y] == side[x]) {
                    return 0;
                }
            }
        }
    }
    int c0 = 0;
    for (int i = 0; i < n; i++) if (side[i] == 0) c0++;
    return c0 > 0 && c0 < n;
}

static void print_best(void) {
    long m = 0;
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++)
            if (v < bestAdj[v][k]) m++;
    printf("%d %ld\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++)
            if (v < bestAdj[v][k]) printf("%d %d\n", v, bestAdj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > MAXD - 1 || D < 1) return 1;
    Dd = d;
    DIAM = D;
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    t0 = (double)clock() / CLOCKS_PER_SEC;

    if (!load_input()) make_kdd();
    if (cost_full() == 0) save_best();

    double T = 0.35;
    int stall = 0;
    const int stallMax = 20000;
    long cur = cost_full();

    while (elapsed() < budget) {
        if (N >= MAXN - 2) break;
        if (cur == 0) {
            if (N > bestN) save_best();
            grow_one();
            logN = 0;
            cur = cost_full();
            stall = 0;
            continue;
        }
        logN = 0;
        if (rndi(100) < 85) do_switch();
        else do_remove();
        do_fill(30);
        long nc = cost_full();
        if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) cur = nc;
        else undo_log();

        if (++stall > stallMax) {
            stall = 0;
            if (bestN > 0) restore_best();
            logN = 0;
            for (int k = 0; k < 4; k++) do_switch();
            do_fill(200);
            double temps[3] = {0.2, 0.35, 0.6};
            T = temps[rndi(3)];
            cur = cost_full();
        }
    }
    if (cur == 0 && N > bestN) save_best();

    if (bestN < 0) {
        make_kdd();
        save_best();
    }
    print_best();
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


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D):
    """A dense structured graph with degree at least d, to be thinned into a valid graph."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the rest."""
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
# Driver. Phases (fractions of T = 0.85 * time_limit):
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials
#   B  thinned dense graph (regular matching thinning or degree reduction + deletion)
#   C  C annealing engine (switches, undo log, vertex insertion) from the best graph
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.18)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.35):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.35):
                r = _deletion_trial(d, D, rn, re, rng, at(0.35))
                if r is None:
                    break
                consider(*r)

    # Phase C: annealing engine in C, started from the best valid graph so far.
    if D >= 2 and best_n <= 1000:
        remaining = at(1.0) - time.monotonic()
        budget = remaining - 2.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=remaining + 0.08 * time_limit)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
