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
#define MAXD 64
#define WMAX 32
#define ITERS 1500

static int d_, D_;
static uint64_t rs;
static clock_t g_deadline;
static int W;

static int N;
static unsigned char side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char adj[MAXN][MAXN];

static int bN;
static unsigned char bside[MAXN];
static int bdeg[MAXN];
static int bnb[MAXN][MAXD];
static unsigned char badj[MAXN][MAXN];

static uint64_t BA[MAXN][WMAX];
static uint64_t BB[MAXN][WMAX];
static uint64_t BC[MAXN][WMAX];

static int in_n, in_m;
static int in_u[MAXN * MAXD], in_v[MAXN * MAXD];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) {
    return (int)(rnd() % (uint64_t)k);
}

static int pc64(uint64_t x) {
#if defined(__GNUC__)
    return __builtin_popcountll(x);
#else
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
#endif
}

static void add_edge(int x, int y) {
    nb[x][deg[x]++] = y;
    nb[y][deg[y]++] = x;
    adj[x][y] = 1;
    adj[y][x] = 1;
}

static void rm_one(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (nb[x][k] == y) {
            nb[x][k] = nb[x][--deg[x]];
            return;
        }
    }
}

static void rm_edge(int x, int y) {
    rm_one(x, y);
    rm_one(y, x);
    adj[x][y] = 0;
    adj[y][x] = 0;
}

/* out[v] = bitset of vertices within distance r of v (first W words). */
static void compute_ball(int r, uint64_t out[][WMAX]) {
    W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(uint64_t) * WMAX);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int round = 0; round < r; round++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = BB[v];
            memcpy(dst, out[v], sizeof(uint64_t) * W);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = out[nb[v][k]];
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        for (int v = 0; v < N; v++) memcpy(out[v], BB[v], sizeof(uint64_t) * W);
    }
}

/* Number of unordered vertex pairs at distance > D_ (unreachable counts). */
static long cost_full(void) {
    compute_ball(D_, BA);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BA[v][w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Add a vertex on the side opposite to a greedily chosen cover of the other side. */
static int add_vertex(void) {
    if (N >= MAXN - 2) return -1;
    int c = rndint(2);
    compute_ball(D_ - 1, BC);
    uint64_t cov[WMAX];
    memset(cov, 0, sizeof cov);
    static int mark[MAXN];
    static int stamp = 0;
    stamp++;
    int cands[MAXN], nca = 0;
    for (int s = 0; s < N; s++) if (side[s] == c) cands[nca++] = s;
    int chosen[MAXD], nc = 0;
    for (int k = 0; k < d_ && nca > 0; k++) {
        long bestsc = -1;
        int bs = -1;
        for (int i = 0; i < nca; i++) {
            int s = cands[i];
            if (mark[s] == stamp) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(BC[s][w] & ~cov[w]);
            long sc = (long)g * 1024 + rndint(1024);
            if (sc > bestsc) { bestsc = sc; bs = s; }
        }
        if (bs < 0) break;
        mark[bs] = stamp;
        chosen[nc++] = bs;
        for (int w = 0; w < W; w++) cov[w] |= BC[bs][w];
    }
    if (nc == 0) return -1;
    int v = N;
    for (int i = 0; i < N; i++) {
        adj[i][v] = 0;
        adj[v][i] = 0;
    }
    N++;
    side[v] = (unsigned char)(1 - c);
    deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= d_) {
            int t = nb[s][rndint(deg[s])];
            rm_edge(s, t);
        }
        add_edge(s, v);
    }
    return v;
}

/* Add cross-side edges between deficient vertices. */
static void fill(void) {
    static int left[MAXN], right[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d_) {
            if (side[v] == 0) left[nl++] = v;
            else right[nr++] = v;
        }
    }
    if (nl == 0 || nr == 0) return;
    long tries = 8L * (nl + nr) + 50;
    for (long t = 0; t < tries; t++) {
        int a = left[rndint(nl)];
        int b = right[rndint(nr)];
        if (deg[a] < d_ && deg[b] < d_ && !adj[a][b]) add_edge(a, b);
    }
}

/* Degree-preserving bipartite double-edge switches minimising bad pairs. */
static int anneal(int iters) {
    static int side0[MAXN];
    int ns0 = 0;
    for (int v = 0; v < N; v++) if (side[v] == 0) side0[ns0++] = v;
    if (ns0 < 2) return 0;
    long cur = cost_full();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() > g_deadline) break;
        int a = side0[rndint(ns0)];
        if (deg[a] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        int c = side0[rndint(ns0)];
        if (c == a || deg[c] == 0) continue;
        int e = nb[c][rndint(deg[c])];
        if (adj[a][e] || adj[c][b]) continue;
        rm_edge(a, b);
        rm_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nw = cost_full();
        if (nw <= cur || (nw == cur + 1 && rnd() % 10 == 0)) {
            cur = nw;
        } else {
            rm_edge(a, e);
            rm_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void save_state(void) {
    bN = N;
    memcpy(bside, side, N);
    memcpy(bdeg, deg, sizeof(int) * N);
    for (int i = 0; i < N; i++) {
        memcpy(bnb[i], nb[i], sizeof(int) * MAXD);
        memcpy(badj[i], adj[i], N);
    }
}

static void restore_state(void) {
    N = bN;
    memcpy(side, bside, N);
    memcpy(deg, bdeg, sizeof(int) * N);
    for (int i = 0; i < N; i++) {
        memcpy(nb[i], bnb[i], sizeof(int) * MAXD);
        memcpy(adj[i], badj[i], N);
    }
}

static void echo_input(void) {
    printf("%d %d\n", in_n, in_m);
    for (int i = 0; i < in_m; i++) printf("%d %d\n", in_u[i], in_v[i]);
}

static void print_best(void) {
    int m = 0;
    for (int u = 0; u < bN; u++)
        for (int k = 0; k < bdeg[u]; k++)
            if (bnb[u][k] > u) m++;
    printf("%d %d\n", bN, m);
    for (int u = 0; u < bN; u++)
        for (int k = 0; k < bdeg[u]; k++) {
            int v = bnb[u][k];
            if (v > u) printf("%d %d\n", u, v);
        }
}

/* Load the input graph into the working state. Returns 1 if it is a valid start. */
static int load_input(void) {
    N = in_n;
    if (d_ < 1 || d_ >= MAXD) return 0;
    for (int i = 0; i < N; i++) {
        deg[i] = 0;
        memset(adj[i], 0, N);
    }
    for (int i = 0; i < in_m; i++) {
        int u = in_u[i], v = in_v[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (adj[u][v]) return 0;
        if (deg[u] >= d_ || deg[v] >= d_) return 0;
        add_edge(u, v);
    }
    for (int i = 0; i < N; i++) side[i] = 2;
    static int stk[MAXN];
    for (int s = 0; s < N; s++) {
        if (side[s] != 2) continue;
        side[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int v = nb[u][k];
                if (side[v] == 2) {
                    side[v] = (unsigned char)(1 - side[u]);
                    stk[sp++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return cost_full() == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    if (scanf("%d %d", &in_n, &in_m) != 2) { printf("0 0\n"); return 0; }
    if (in_n < 1 || in_n > MAXN - 2 || in_m < 0 || in_m > MAXN * MAXD) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < in_m; i++) {
        if (scanf("%d %d", &in_u[i], &in_v[i]) != 2) { printf("0 0\n"); return 0; }
    }

    if (!load_input()) {
        echo_input();
        return 0;
    }
    save_state();

    g_deadline = clock() + (clock_t)(budget * CLOCKS_PER_SEC);
    while (clock() < g_deadline) {
        restore_state();
        int v = add_vertex();
        if (v < 0) continue;
        fill();
        if (anneal(ITERS)) save_state();
    }
    print_best();
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


# ----------------------------------------------------------------------------
# Twin duplication.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.97 * time_limit
    deadline = start + 0.90 * time_limit
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
            grow_end = start + 0.08 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.15 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Main stage: C annealing engine repeatedly adds one vertex to the best
    # valid graph, repairs it with degree-preserving switches, and keeps successes.
    if D >= 2:
        budget = deadline - time.monotonic() - 1.0
        if budget > 0.5:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed, round(budget, 2)],
                    stdin_graph=(best_n, list(best_e)),
                    timeout=max(1.0, hard_end - time.monotonic()),
                )
                cn, ce = lib.parse_graph_text(out)
                consider(cn, ce)
            except (RuntimeError, ValueError, OSError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
