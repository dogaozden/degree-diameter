import itertools
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 8192
#define MAXW ((MAXN + 63) / 64)
#define MAXCH 256

typedef uint64_t u64;

static int DD, DIAM, N, W;
static int *deg, *adj, *col;
static int *sdeg, *sadj, *scol;
static int *bdeg, *badj, *bcol;
static int bestN = 0;
static u64 *ballA, *ballB;
static int *qbuf, *Lbuf, *Rbuf;
static u64 rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd() % (u64)n);
}

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *p = adj + (size_t)u * DD;
    for (int i = 0; i < deg[u]; i++)
        if (p[i] == v) return 1;
    return 0;
}

static void add_half(int u, int v) {
    adj[(size_t)u * DD + deg[u]] = v;
    deg[u]++;
}

static void del_half(int u, int v) {
    int *p = adj + (size_t)u * DD;
    for (int i = 0; i < deg[u]; i++) {
        if (p[i] == v) {
            p[i] = p[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    add_half(u, v);
    add_half(v, u);
}

static void del_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
}

/* Bitset of vertices within distance radius of each vertex. Returns buffer with stride W. */
static u64 *compute_balls(int radius) {
    int w = W;
    u64 *src = ballA, *dst = ballB;
    memset(src, 0, sizeof(u64) * (size_t)N * w);
    for (int v = 0; v < N; v++)
        src[(size_t)v * w + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < radius; r++) {
        for (int v = 0; v < N; v++) {
            u64 *dv = dst + (size_t)v * w;
            const u64 *sv = src + (size_t)v * w;
            memcpy(dv, sv, sizeof(u64) * w);
            const int *p = adj + (size_t)v * DD;
            for (int i = 0; i < deg[v]; i++) {
                const u64 *su = src + (size_t)p[i] * w;
                for (int k = 0; k < w; k++) dv[k] |= su[k];
            }
        }
        u64 *t = src;
        src = dst;
        dst = t;
    }
    return src;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long cost(void) {
    if (N <= 1) return 0;
    u64 *b = compute_balls(DIAM);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        const u64 *s = b + (size_t)v * W;
        int cnt = 0;
        for (int k = 0; k < W; k++) cnt += popc(s[k]);
        bad += N - cnt;
    }
    return bad / 2;
}

static int bipartite_color(void) {
    int ok = 1;
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qbuf[qt++] = s;
        while (qh < qt) {
            int u = qbuf[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[(size_t)u * DD + i];
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    qbuf[qt++] = v;
                } else if (col[v] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    return ok;
}

/* Add a vertex on `side`, joined greedily to a cover of the other side. */
static void add_vertex(int side) {
    if (N >= MAXN || N < 1) return;
    int w = W;
    u64 *b = compute_balls(DIAM - 1);
    u64 covered[MAXW];
    memset(covered, 0, sizeof(u64) * w);
    int chosen[MAXCH];
    int nch = 0;
    for (int t = 0; t < DD && t < MAXCH; t++) {
        long bestKey = -1;
        int best = -1;
        for (int c = 0; c < N; c++) {
            if (col[c] != 1 - side) continue;
            int used = 0;
            for (int i = 0; i < nch; i++)
                if (chosen[i] == c) { used = 1; break; }
            if (used) continue;
            const u64 *bc = b + (size_t)c * w;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(bc[k] & ~covered[k]);
            if (g == 0) continue;
            long key = (long)g * 4096 + rndint(4096);
            if (key > bestKey) {
                bestKey = key;
                best = c;
            }
        }
        if (best < 0) break;
        chosen[nch++] = best;
        const u64 *bc = b + (size_t)best * w;
        for (int k = 0; k < w; k++) covered[k] |= bc[k];
    }
    int v = N;
    N++;
    W = (N + 63) / 64;
    col[v] = side;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int c = chosen[i];
        if (deg[c] >= DD) {
            int t = adj[(size_t)c * DD + rndint(deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
}

/* Add random cross-side edges between deficient vertices. */
static void fill(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= DD) continue;
        if (col[v] == 0) Lbuf[nl++] = v;
        else Rbuf[nr++] = v;
    }
    if (nl == 0 || nr == 0) return;
    long tries = 30L * (nl + nr);
    for (long t = 0; t < tries; t++) {
        int a = Lbuf[rndint(nl)];
        int b = Rbuf[rndint(nr)];
        if (deg[a] >= DD || deg[b] >= DD) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
    }
}

/* Degree-preserving bipartite switches minimising bad pairs. Returns 1 if cost reaches 0. */
static int anneal(long iters, double deadline, int T) {
    long cur = cost();
    for (long it = 0; it < iters; it++) {
        if (cur == 0) return 1;
        if ((it & 15) == 0 && now() > deadline) break;
        int a = rndint(N);
        if (deg[a] == 0) continue;
        int b = adj[(size_t)a * DD + rndint(deg[a])];
        int c = rndint(N);
        if (c == a || col[c] != col[a] || deg[c] == 0) continue;
        int e = adj[(size_t)c * DD + rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        if (nc <= cur || (nc - cur <= 2 && rndint(1000) < T)) {
            cur = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void snapshot(int *d_, int *a_, int *c_) {
    memcpy(d_, deg, sizeof(int) * N);
    memcpy(a_, adj, sizeof(int) * (size_t)N * DD);
    memcpy(c_, col, sizeof(int) * N);
}

static void load(const int *d_, const int *a_, const int *c_, int n) {
    N = n;
    W = (N + 63) / 64;
    memcpy(deg, d_, sizeof(int) * n);
    memcpy(adj, a_, sizeof(int) * (size_t)n * DD);
    memcpy(col, c_, sizeof(int) * n);
}

static void save_best(void) {
    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * N);
    memcpy(badj, adj, sizeof(int) * (size_t)N * DD);
    memcpy(bcol, col, sizeof(int) * N);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (DD < 1 || DD > 64 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double deadline = t0 + budget;

    deg = calloc(MAXN, sizeof(int));
    col = calloc(MAXN, sizeof(int));
    adj = calloc((size_t)MAXN * DD, sizeof(int));
    sdeg = calloc(MAXN, sizeof(int));
    scol = calloc(MAXN, sizeof(int));
    sadj = calloc((size_t)MAXN * DD, sizeof(int));
    bdeg = calloc(MAXN, sizeof(int));
    bcol = calloc(MAXN, sizeof(int));
    badj = calloc((size_t)MAXN * DD, sizeof(int));
    ballA = calloc((size_t)MAXN * MAXW, sizeof(u64));
    ballB = calloc((size_t)MAXN * MAXW, sizeof(u64));
    qbuf = calloc(MAXN, sizeof(int));
    Lbuf = calloc(MAXN, sizeof(int));
    Rbuf = calloc(MAXN, sizeof(int));

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n < 0 || n > MAXN) n = 0;
    N = n;
    W = (N + 63) / 64;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= DD || deg[v] >= DD || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    if (N == 0 || !bipartite_color()) {
        printf("0 0\n");
        return 0;
    }

    if (cost() == 0) save_best();

    int tchoice[3] = {0, 20, 60};
    int fails = 0;
    int sn;
    while (now() < deadline) {
        sn = N;
        snapshot(sdeg, sadj, scol);
        int side = rndint(2);
        add_vertex(side);
        fill();
        int T = tchoice[rndint(3)];
        int ok = anneal(3000, deadline, T);
        if (ok) {
            if (N > bestN) save_best();
            fails = 0;
        } else {
            load(sdeg, sadj, scol, sn);
            fails++;
            if (fails > 200) {
                if (bestN > 0) load(bdeg, badj, bcol, bestN);
                fails = 0;
            }
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bdeg[v];
    m2 /= 2;
    printf("%d %ld\n", bestN, m2);
    for (int u = 0; u < bestN; u++) {
        for (int i = 0; i < bdeg[u]; i++) {
            int v = badj[(size_t)u * DD + i];
            if (u < v) printf("%d %d\n", u, v);
        }
    }
    return 0;
}
"""


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
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


# ----------------------------------------------------------------------------
# New construction: random voltage lifts of small d-regular bipartite base
# multigraphs over Z_m, found by hill-climbing the number of bad pairs.
# ----------------------------------------------------------------------------

def _climb(p, m, d, D, end, rng):
    """Search voltages for a lift with 2*p*m vertices. Returns (n, edges) if diameter <= D, else None."""
    base_n = 2 * p
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            darts.append([i, p + perm[i], rng.randrange(m)])
    expected = len(darts) * m

    def evaluate():
        n, edges = lib.voltage_lift(base_n, [tuple(x) for x in darts], m)
        pen = expected - len(edges)  # collisions lose edges (degree drops, still valid)
        bad = lib.bad_pairs(n, edges, D)
        return bad + 20 * pen, n, edges

    cur, n, e = evaluate()
    while cur > 0 and time.monotonic() < end:
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(m)
        c, n2, e2 = evaluate()
        if c <= cur:
            cur, n, e = c, n2, e2
        else:
            darts[idx][2] = old
    if cur == 0:
        return n, e
    return None


def _lift_search(n, edges, d, D, deadline, rng):
    """Repeatedly try lifts of growing order; return the largest valid graph found."""
    cur_n, cur_e = n, list(edges)
    ps = [2, 3, 4, 5, 6, 7]
    while time.monotonic() < deadline:
        p = rng.choice(ps)
        m = cur_n // (2 * p) + 1 + rng.randrange(2)  # lift order 2*p*m > cur_n
        slice_end = min(deadline, time.monotonic() + 4.0)
        res = _climb(p, m, d, D, slice_end, rng)
        if res is not None:
            rn, re = res
            if rn > cur_n and lib.is_valid(rn, re, d, D):
                cur_n, cur_e = rn, list(re)
    return cur_n, cur_e


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

    # Structured base: W(q) for D >= 4, PG(2,q) for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
            consider(n1, e1)

    # New search: voltage lifts over cyclic groups of small bipartite base multigraphs.
    if D >= 2 and d >= 2:
        lift_end = start + 0.5 * time_limit
        ln, le = _lift_search(best_n, best_e, d, D, lift_end, rng)
        consider(ln, le)

    # C annealing from the best graph found so far.
    if D >= 2 and d >= 2:
        budget = start + 0.9 * time_limit - time.monotonic() - 3.0
        if budget > 1.0:
            try:
                txt = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(txt)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
