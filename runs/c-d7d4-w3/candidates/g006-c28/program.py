import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: grow a valid graph by adding vertices, then repair it with
# simulated annealing over degree-preserving moves that minimise the number of
# vertex pairs at distance > D. Bipartiteness and the degree cap are kept by
# every move, so only the diameter cost has to reach zero.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 26
#define MAXD 80

static int N, W, DMAX, DIAM;
static int col[MAXN], deg[MAXN];
static int adj[MAXN][MAXD];
static unsigned char mat[MAXN][MAXN];
static uint64_t ballA[MAXN][MAXW], ballB[MAXN][MAXW];
static int side[2][MAXN], sideCnt[2];
static int sN, sCol[MAXN], sDeg[MAXN], sAdj[MAXN][MAXD];
static int haveBest = 0;
static int timedOut = 0;
static double deadline;
static uint64_t rs;
static int qbuf[MAXN];

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void rem_from(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_e(int u, int v) {
    mat[u][v] = 1;
    mat[v][u] = 1;
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_e(int u, int v) {
    mat[u][v] = 0;
    mat[v][u] = 0;
    rem_from(u, v);
    rem_from(v, u);
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static int cost(void) {
    int n = N, w = W;
    for (int v = 0; v < n; v++) {
        memset(ballA[v], 0, sizeof(uint64_t) * (size_t)w);
        ballA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = ballB[v];
            memcpy(dst, ballA[v], sizeof(uint64_t) * (size_t)w);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = ballA[adj[v][i]];
                for (int k = 0; k < w; k++) dst[k] |= src[k];
            }
        }
        for (int v = 0; v < n; v++)
            memcpy(ballA[v], ballB[v], sizeof(uint64_t) * (size_t)w);
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += pc64(ballA[v][k]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

typedef struct {
    int nr, na;
    int ru[2], rv[2], au[2], av[2];
} Move;

static void apply_move(const Move *m) {
    for (int i = 0; i < m->nr; i++) del_e(m->ru[i], m->rv[i]);
    for (int i = 0; i < m->na; i++) add_e(m->au[i], m->av[i]);
}

static void undo_move(const Move *m) {
    for (int i = 0; i < m->na; i++) del_e(m->au[i], m->av[i]);
    for (int i = 0; i < m->nr; i++) add_e(m->ru[i], m->rv[i]);
}

static int pick_side(int s, int needdeg) {
    if (sideCnt[s] == 0) return -1;
    for (int t = 0; t < 30; t++) {
        int c = side[s][rndint(sideCnt[s])];
        if (!needdeg || deg[c] > 0) return c;
    }
    return -1;
}

static int propose(Move *m) {
    m->nr = 0;
    m->na = 0;
    if (N < 2 || sideCnt[0] == 0 || sideCnt[1] == 0) return 0;
    int t = rndint(10);
    if (t < 4) {
        /* Re-hang one endpoint of an edge onto a deficient vertex of the same side. */
        int s = rndint(2);
        int x = pick_side(s, 1);
        if (x < 0) return 0;
        int y = adj[x][rndint(deg[x])];
        int x2 = -1;
        for (int tr = 0; tr < 40; tr++) {
            int c = side[s][rndint(sideCnt[s])];
            if (c != x && deg[c] < DMAX && !mat[c][y]) { x2 = c; break; }
        }
        if (x2 < 0) return 0;
        m->nr = 1; m->ru[0] = x; m->rv[0] = y;
        m->na = 1; m->au[0] = x2; m->av[0] = y;
        return 1;
    }
    if (t < 8) {
        /* Degree-preserving double-edge switch. */
        int s = rndint(2);
        int x = pick_side(s, 1);
        int z = pick_side(s, 1);
        if (x < 0 || z < 0 || x == z) return 0;
        int y = adj[x][rndint(deg[x])];
        int w = adj[z][rndint(deg[z])];
        if (y == w || mat[x][w] || mat[z][y]) return 0;
        m->nr = 2; m->ru[0] = x; m->rv[0] = y; m->ru[1] = z; m->rv[1] = w;
        m->na = 2; m->au[0] = x; m->av[0] = w; m->au[1] = z; m->av[1] = y;
        return 1;
    }
    /* Add an edge between two deficient vertices on opposite sides (never hurts). */
    for (int tr = 0; tr < 40; tr++) {
        int a = side[0][rndint(sideCnt[0])];
        int b = side[1][rndint(sideCnt[1])];
        if (deg[a] < DMAX && deg[b] < DMAX && !mat[a][b]) {
            m->na = 1; m->au[0] = a; m->av[0] = b;
            return 1;
        }
    }
    return 0;
}

static int anneal(long iters, double T0, double T1) {
    int cur = cost();
    if (cur == 0) return 1;
    Move m;
    for (long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && now_sec() > deadline) {
            timedOut = 1;
            return 0;
        }
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!propose(&m)) continue;
        apply_move(&m);
        int nw = cost();
        int delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            undo_move(&m);
        }
    }
    return 0;
}

static void rebuild_sides(void) {
    sideCnt[0] = 0;
    sideCnt[1] = 0;
    for (int v = 0; v < N; v++) side[col[v]][sideCnt[col[v]]++] = v;
}

static void save_state(void) {
    sN = N;
    for (int v = 0; v < N; v++) {
        sCol[v] = col[v];
        sDeg[v] = deg[v];
        memcpy(sAdj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
    haveBest = 1;
}

static void load_state(void) {
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) mat[v][adj[v][i]] = 0;
    N = sN;
    W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        col[v] = sCol[v];
        deg[v] = sDeg[v];
        memcpy(adj[v], sAdj[v], sizeof(int) * (size_t)deg[v]);
    }
    for (int v = 0; v < N; v++)
        for (int i = 0; i < deg[v]; i++) mat[v][adj[v][i]] = 1;
    rebuild_sides();
}

static void add_vertex(int c) {
    int v = N++;
    W = (N + 63) >> 6;
    col[v] = c;
    deg[v] = 0;
    side[c][sideCnt[c]++] = v;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    double t0 = now_sec();
    double budget = tl * 0.9 - 0.5;
    if (budget < 0.3) budget = 0.3;
    deadline = t0 + budget;
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    DMAX = d;
    DIAM = D;

    int n, m;
    if (d < 1 || d >= MAXD || D < 1 || scanf("%d %d", &n, &m) != 2 ||
        n < 1 || n > MAXN || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) { col[v] = -1; deg[v] = 0; }
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || mat[u][v] ||
            deg[u] >= DMAX || deg[v] >= DMAX) {
            ok = 0;
            break;
        }
        add_e(u, v);
    }
    if (ok) {
        for (int s = 0; s < N && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            qbuf[qt++] = s;
            while (qh < qt && ok) {
                int x = qbuf[qh++];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adj[x][i];
                    if (col[y] == -1) {
                        col[y] = 1 - col[x];
                        qbuf[qt++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (ok) {
        rebuild_sides();
        if (sideCnt[0] == 0 || sideCnt[1] == 0) ok = 0;
    }
    if (ok && anneal(300000, 1.0, 0.1)) save_state();

    if (haveBest) {
        long iters = 20000;
        while (!timedOut && now_sec() < deadline && N < MAXN - 1) {
            add_vertex(rndint(2));
            int r = anneal(iters, 1.2, 0.12);
            if (r == 1) {
                save_state();
                iters = 20000;
                continue;
            }
            if (timedOut) break;
            load_state();
            if (iters < 400000) iters *= 2;
            Move mv;
            int kk = 5 + rndint(20);
            for (int i = 0; i < kk; i++)
                if (propose(&mv)) apply_move(&mv);
        }
        load_state();
        int em = 0;
        for (int v = 0; v < N; v++)
            for (int i = 0; i < deg[v]; i++)
                if (adj[v][i] > v) em++;
        printf("%d %d\n", N, em);
        for (int v = 0; v < N; v++)
            for (int i = 0; i < deg[v]; i++)
                if (adj[v][i] > v) printf("%d %d\n", v, adj[v][i]);
    } else {
        printf("0 0\n");
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
    """A dense structured graph whose degree is at least d; later thinned to validity."""
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
# Thinning a dense structured graph into a valid one.
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
# Driver: structured base and Python growth first, then the C annealing engine
# grows the best valid graph by one vertex at a time.
# ----------------------------------------------------------------------------

def _c_grow(best_n, best_e, d, D, seed, budget):
    """Run the C engine from (best_n, best_e) for about `budget` seconds. Returns (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                     stdin_graph=(best_n, best_e), timeout=budget + 2.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = 0.92 * time_limit

    def at(f):
        return start + f * span

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

    # Structured base (W(q) for D >= 4, PG(2, q) for D = 3) grown by cover vertices.
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

    # Calibration cases with a known optimum return at once.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Randomized twin / cover pipelines.
    if D >= 2:
        trial_end = at(0.14)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Thinned dense graph (degree reduction plus vertex deletion).
    if D >= 2 and time.monotonic() < at(0.18):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.26):
                r = _deletion_trial(d, D, rn, re, rng, at(0.26))
                if r is None:
                    break
                consider(*r)

    # C annealing engine: grows the best valid graph for the rest of the budget.
    if D >= 2 and time.monotonic() < at(0.80):
        cb = start + span - time.monotonic() - 3.0
        if cb >= 2.0:
            try:
                cn, ce = _c_grow(best_n, best_e, d, D, seed, cb)
                consider(cn, ce)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
