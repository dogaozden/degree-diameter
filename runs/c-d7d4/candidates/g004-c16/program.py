import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: bitset-based simulated annealing over bipartite edge
# switches, with vertex growth. Each growth step adds a vertex joined to a
# greedy cover of the other side's distance-(D-1) balls, fills spare degree,
# then anneals to restore diameter D. Accepted states are always valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1200
#define MAXD 60
#define WMAX ((MAXN + 63) / 64)
#define MAXM (MAXN * MAXD / 2 + 8)
#define ITERS 6000
#define T0 1.0
#define T1 0.05

typedef uint64_t u64;

typedef struct {
    int n;
    int col[MAXN];
    int m;
    int eu[MAXM];
    int ev[MAXM];
} Snap;

static int d, D;
static int N;
static int col[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char am[MAXN][MAXN];
static u64 bufA[MAXN][WMAX], bufB[MAXN][WMAX];
static Snap curS, bestS;
static u64 rs = 88172645463325252ULL;
static double budget_sec;
static clock_t clk0;

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int time_up(void) {
    return (double)(clock() - clk0) / CLOCKS_PER_SEC >= budget_sec;
}

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Bitmask of vertices within distance r of each vertex (after r rounds). */
static u64 (*compute_balls(int r))[WMAX] {
    int wn = (N + 63) / 64;
    u64 (*A)[WMAX] = bufA;
    u64 (*B)[WMAX] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < wn; w++) A[v][w] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < wn; w++) B[v][w] = A[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const u64 *src = A[nb[v][i]];
                for (int w = 0; w < wn; w++) B[v][w] |= src[w];
            }
        }
        u64 (*t)[WMAX] = A;
        A = B;
        B = t;
    }
    return A;
}

/* Number of unordered vertex pairs at distance more than D. */
static long long bad_pairs(void) {
    int wn = (N + 63) / 64;
    u64 (*A)[WMAX] = compute_balls(D);
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < wn; w++) c += pc64(A[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

static void rm_nb(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) {
            nb[u][i] = nb[u][--deg[u]];
            return;
        }
    }
}

static void add_e(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    am[u][v] = 1;
    am[v][u] = 1;
}

static void del_e(int u, int v) {
    rm_nb(u, v);
    rm_nb(v, u);
    am[u][v] = 0;
    am[v][u] = 0;
}

static void clear_graph(void) {
    for (int u = 0; u < N; u++) {
        for (int i = 0; i < deg[u]; i++) am[u][nb[u][i]] = 0;
        deg[u] = 0;
    }
    N = 0;
}

static void make_kdd(void) {
    N = 2 * d;
    for (int v = 0; v < N; v++) {
        col[v] = (v < d) ? 0 : 1;
        deg[v] = 0;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_e(i, d + j);
}

static void save_snap(Snap *s) {
    s->n = N;
    memcpy(s->col, col, sizeof(int) * N);
    s->m = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = nb[u][i];
            if (u < v) {
                s->eu[s->m] = u;
                s->ev[s->m] = v;
                s->m++;
            }
        }
}

static void load_snap(const Snap *s) {
    clear_graph();
    N = s->n;
    memcpy(col, s->col, sizeof(int) * N);
    for (int i = 0; i < s->m; i++) add_e(s->eu[i], s->ev[i]);
}

static int read_graph_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 < 1 || n0 >= MAXN - 2 || m0 < 0) return 0;
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (am[u][v] || deg[u] >= d || deg[v] >= d) return 0;
        add_e(u, v);
    }
    return 1;
}

static int color_graph(void) {
    static int q[MAXN], seen[MAXN];
    memset(seen, 0, sizeof(int) * N);
    for (int s = 0; s < N; s++) {
        if (seen[s]) continue;
        int h = 0, t = 0;
        seen[s] = 1;
        col[s] = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!seen[v]) {
                    seen[v] = 1;
                    col[v] = 1 - col[u];
                    q[t++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add one vertex on the opposite side of `side`, joined to a greedy cover of `side`. */
static void add_cover_vertex(int side) {
    u64 (*A)[WMAX] = compute_balls(D - 1);
    int wn = (N + 63) / 64;
    u64 cov[WMAX];
    memset(cov, 0, sizeof cov);
    static int used[MAXN];
    memset(used, 0, sizeof(int) * N);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == side) cand[nc++] = v;
    int chosen[MAXD];
    int k = 0;
    int covcount = 0;
    while (k < d && covcount < N) {
        int best = -1, bestg = 0, ties = 0;
        for (int i = 0; i < nc; i++) {
            int c = cand[i];
            if (used[c]) continue;
            int g = 0;
            for (int w = 0; w < wn; w++) g += pc64(A[c][w] & ~cov[w]);
            if (g > bestg) {
                bestg = g;
                best = c;
                ties = 1;
            } else if (g == bestg && g > 0) {
                ties++;
                if (rndint(ties) == 0) best = c;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[k++] = best;
        for (int w = 0; w < wn; w++) cov[w] |= A[best][w];
        covcount = 0;
        for (int w = 0; w < wn; w++) covcount += pc64(cov[w]);
    }
    if (k == 0) return;

    int v = N;
    N++;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < k; i++) {
        int s = chosen[i];
        if (deg[s] >= d) {
            int t = nb[s][rndint(deg[s])];
            del_e(s, t);
        }
        add_e(s, v);
    }
}

/* Join deficient opposite-side vertices at random (only shortens distances). */
static void fill_spare(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= d) continue;
        if (col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = R[j];
            if (deg[b] < d && !am[a][b]) add_e(a, b);
        }
    }
}

/* Simulated annealing over bipartite double-edge switches minimising bad pairs. */
static long long anneal(long long cur, int iters, double t0, double t1) {
    static int side0[MAXN];
    int ns = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0) side0[ns++] = v;
    if (ns < 2) return cur;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && time_up()) break;
        double T = t0 * pow(t1 / t0, (double)it / (double)iters);
        int a = side0[rndint(ns)];
        int c = side0[rndint(ns)];
        if (c == a || deg[a] == 0 || deg[c] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (am[a][e] || am[c][b]) continue;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        long long nw = bad_pairs();
        long long diff = nw - cur;
        if (diff <= 0 || rnd01() < exp(-(double)diff / T)) {
            cur = nw;
        } else {
            del_e(a, e);
            del_e(c, b);
            add_e(a, b);
            add_e(c, e);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_sec = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    clk0 = clock();

    if (d < 1 || d > MAXD - 2 || D < 2) {
        printf("1 0\n");
        return 0;
    }

    if (!read_graph_input() || !color_graph()) {
        clear_graph();
        make_kdd();
    }

    long long cost = bad_pairs();
    if (cost > 0) cost = anneal(cost, 20000, 1.0, 0.05);
    if (cost > 0) {
        clear_graph();
        make_kdd();
    }
    save_snap(&bestS);

    while (!time_up() && N + 2 < MAXN) {
        save_snap(&curS);
        add_cover_vertex(rndint(2));
        fill_spare();
        long long c = bad_pairs();
        c = anneal(c, ITERS, T0, T1);
        if (c == 0) {
            if (N > bestS.n) save_snap(&bestS);
        } else {
            load_snap(&curS);
        }
    }

    printf("%d %d\n", bestS.n, bestS.m);
    for (int i = 0; i < bestS.m; i++) printf("%d %d\n", bestS.eu[i], bestS.ev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    # Short randomized twin-duplication pipelines for a starting graph.
    prep_end = start + 0.3 * time_limit
    if D >= 2:
        while time.monotonic() < prep_end:
            if best_n > base_n and rng.random() < 0.5:
                bn, be = best_n, list(best_e)
            else:
                bn, be = base_n, list(base_e)
            n, e = _trial(bn, be, d, D, rng, prep_end)
            consider(n, e)

    # C annealing stage: grow the best graph found so far. Skipped when the
    # Moore bound already matches it (nothing to gain) or the budget is tiny.
    ceiling = lib.moore_bound(d, D)
    if D >= 2 and d <= 40 and best_n < ceiling and time_limit >= 8:
        elapsed = time.monotonic() - start
        budget = 0.85 * time_limit - elapsed - 2.0
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 6.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
