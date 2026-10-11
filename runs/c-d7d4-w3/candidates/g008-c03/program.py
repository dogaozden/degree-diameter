import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-accelerated annealing with vertex insertion.
#
# The state is a bipartite graph with max degree d. The cost is the number of
# vertex pairs at distance > D, computed by bitset ball expansion. Moves are
# degree-preserving bipartite double-edge switches (Metropolis on the cost).
# Growth adds one vertex on a random side, joined to d opposite vertices; an
# edge is first removed from any opposite vertex already at degree d, so all
# degrees stay <= d. Deficient cross pairs are then filled greedily, which can
# only lower the cost. The best valid state is kept and restored after failed
# annealing runs, followed by a random kick.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define WMAX 16
#define MAXD 16

typedef struct {
    int n;
    int deg[MAXN];
    int nb[MAXN][MAXD];
    int side[MAXN];
} State;

static int DEGCAP, DIAM, N;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static int side[MAXN];
static uint64_t R[2][MAXN][WMAX];
static State best;
static int have_best = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static clock_t T0;
static double BUDGET = 1.0;
static int EU[MAXN * MAXD], EV[MAXN * MAXD];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) {
    return (double)(clock() - T0) / (double)CLOCKS_PER_SEC >= BUDGET;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) return 1;
    return 0;
}

static void rem_dir(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void rem_edge(int a, int b) {
    rem_dir(a, b);
    rem_dir(b, a);
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long cost_full(void) {
    if (N <= 1) return 0;
    int Wc = (N + 63) >> 6;
    int cur = 0;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < Wc; w++) R[0][v][w] = 0;
        R[0][v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < DIAM; s++) {
        int nx = cur ^ 1;
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < Wc; w++) {
                uint64_t x = R[cur][v][w];
                for (int k = 0; k < deg[v]; k++) x |= R[cur][nb[v][k]][w];
                R[nx][v][w] = x;
            }
        }
        cur = nx;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < Wc; w++) c += popc(R[cur][v][w]);
        bad += N - c;
    }
    return bad / 2;
}

static int pick_side(int s) {
    for (int t = 0; t < 10000; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Bipartite double-edge switch: a-b, c-e  ->  a-e, c-b (a, c on side 0). */
static int do_switch(int *ra, int *rb, int *rc, int *re) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = nb[a][rndint(deg[a])];
    int e = nb[c][rndint(deg[c])];
    if (b == e || has_edge(a, e) || has_edge(c, b)) return 0;
    rem_edge(a, b);
    rem_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    *ra = a; *rb = b; *rc = c; *re = e;
    return 1;
}

static void undo_switch(int a, int b, int c, int e) {
    rem_edge(a, e);
    rem_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Greedy addition of edges between deficient cross pairs. Never increases the cost. */
static int fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0, added = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEGCAP) {
            if (side[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle_int(L0, n0);
    shuffle_int(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg[a] < DEGCAP; j++) {
            int b = L1[j];
            if (deg[b] >= DEGCAP || has_edge(a, b)) continue;
            add_edge(a, b);
            added++;
        }
    }
    return added;
}

/* Insert one vertex on a random side, joined to up to DEGCAP opposite vertices. */
static void grow(void) {
    static int lst[MAXN], full[MAXN];
    if (N >= MAXN - 1) return;
    int c = rndint(2);
    int v = N++;
    deg[v] = 0;
    side[v] = c;
    int nl = 0, nf = 0;
    for (int u = 0; u < v; u++) {
        if (side[u] == c) continue;
        if (deg[u] < DEGCAP) lst[nl++] = u;
        else full[nf++] = u;
    }
    shuffle_int(lst, nl);
    shuffle_int(full, nf);
    for (int i = 0; i < nf; i++) lst[nl + i] = full[i];
    int total = nl + nf;
    for (int i = 0; i < total && i < DEGCAP; i++) {
        int u = lst[i];
        if (deg[u] >= DEGCAP) {
            int w = nb[u][rndint(deg[u])];
            rem_edge(u, w);
        }
        add_edge(v, u);
    }
}

static void save_state(State *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof(deg));
    memcpy(s->nb, nb, sizeof(nb));
    memcpy(s->side, side, sizeof(side));
}

static void load_state(const State *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof(deg));
    memcpy(nb, s->nb, sizeof(nb));
    memcpy(side, s->side, sizeof(side));
}

/* Metropolis-style switch annealing on the cost. Returns the final cost. */
static long long anneal(long long cur, int iters) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && timeup()) break;
        int a, b, c, e;
        if (!do_switch(&a, &b, &c, &e)) continue;
        long long nc = cost_full();
        if (nc <= cur || (nc == cur + 1 && rnd01() < 0.05)) cur = nc;
        else undo_switch(a, b, c, e);
    }
    return cur;
}

static void kick(int k) {
    int a, b, c, e;
    for (int i = 0; i < k; i++) do_switch(&a, &b, &c, &e);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    BUDGET = atof(argv[4]);
    rs ^= (seed + 1ULL) * 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    T0 = clock();

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n <= 1 || n > MAXN || d < 1 || d > MAXD || DIAM < 1 || m < 0 || m > MAXN * MAXD / 2) {
        printf("0 0\n");
        return 0;
    }
    DEGCAP = d;
    N = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= d || deg[v] >= d || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    static int q[MAXN];
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int x = q[h++];
            for (int k = 0; k < deg[x]; k++) {
                int y = nb[x][k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    q[t++] = y;
                } else if (side[y] == side[x]) {
                    printf("0 0\n");
                    return 0;
                }
            }
        }
    }

    long long cost = cost_full();
    if (cost == 0) {
        save_state(&best);
        have_best = 1;
    }
    while (!timeup()) {
        if (cost == 0) {
            if (!have_best || N > best.n) {
                save_state(&best);
                have_best = 1;
            }
            grow();
            fill();
            cost = cost_full();
            continue;
        }
        cost = anneal(cost, 3000);
        if (cost != 0 && have_best) {
            load_state(&best);
            kick(4 + rndint(12));
            cost = cost_full();
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    load_state(&best);
    int me = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (nb[v][k] > v) me++;
    printf("%d %d\n", N, me);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (nb[v][k] > v) printf("%d %d\n", v, nb[v][k]);
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Local search for a cover of `full` by at most d candidates (swap moves, light annealing)."""
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured small base (W(q) or PG(2,q)) grown, twin trials
#   B  thinned dense graph (degree reduction + vertex deletion)
#   C  C engine: bitset switch-annealing with vertex insertion, started from the
#      best valid graph. Skipped when the Moore bound is already reached.
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

    # Phase A: structured small base, then randomized growth trials.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.04), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: thinned dense graph, repeated.
    if D >= 2 and time.monotonic() < at(0.20):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.20):
                r = _deletion_trial(d, D, rn, re, rng, at(0.20))
                if r is None:
                    break
                consider(*r)

    # Phase C: C annealing engine from the best valid graph.
    moore = lib.moore_bound(d, D)
    if D >= 2 and d <= 16 and best_n < moore:
        budget = start + 0.88 * time_limit - time.monotonic() - 2.0
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
