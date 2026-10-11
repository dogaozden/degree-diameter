import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-cost simulated annealing with vertex insertion.
#
# The state is a bipartite graph with max degree d. Its cost is the number of
# vertex pairs at distance > D, computed exactly with bitsets. Moves are bipartite
# double-edge switches (degrees preserved) and greedy fills of deficient
# cross-side pairs. When the cost reaches 0 the graph is saved and one vertex is
# inserted: its neighbourhood is a greedy cover of the other side by radius-(D-1)
# balls, so the new vertex starts with distance <= D to everything. The annealer
# then repairs the graph. Only valid (cost 0) graphs are ever output.
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
#define MAXE (MAXN * MAXD / 2)
#define EPOCH 20000
#define THI 1.2
#define TLO 0.15

static int dd, DD, N;
static int adjv[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static uint64_t bufA[MAXN * MAXW];
static uint64_t bufB[MAXN * MAXW];
static int side0[MAXN];
static int n0;
static uint64_t rs = 88172645463325252ULL;
static int bestN = 0, bestM = 0, bestValid = 0;
static int bestU[MAXE], bestV[MAXE];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++)
        if (adjv[a][j] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void del_arc(int a, int b) {
    for (int j = 0; j < deg[a]; j++) {
        if (adjv[a][j] == b) {
            adjv[a][j] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

static int nwords(void) { return (N + 63) >> 6; }

static void rebuild_side0(void) {
    n0 = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == 0) side0[n0++] = v;
}

/* Bitmask of all vertices within distance r of each vertex (row stride nwords()). */
static uint64_t *compute_ball(int r) {
    int nw = nwords();
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)nw);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * nw + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * nw;
            memcpy(o, cur + (size_t)v * nw, sizeof(uint64_t) * (size_t)nw);
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *s = cur + (size_t)adjv[v][j] * nw;
                for (int w = 0; w < nw; w++) o[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DD (unreachable pairs included). */
static long cost_now(void) {
    int nw = nwords();
    uint64_t *b = compute_ball(DD);
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *row = b + (size_t)v * nw;
        for (int w = 0; w < nw; w++) c += popc64(row[w]);
        bad += N - c;
    }
    return bad / 2;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Greedily join deficient opposite-side vertices in random order. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < dd) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        if (deg[a] >= dd) continue;
        for (int j = 0; j < nr; j++) {
            int b = R[j];
            if (deg[b] < dd && !has_edge(a, b)) {
                add_edge(a, b);
                break;
            }
        }
    }
}

/* Insert a vertex whose neighbourhood greedily covers the other side with radius D-1 balls. */
static void add_vertex(void) {
    int nw = nwords();
    uint64_t *b = compute_ball(DD - 1);
    int c = rndint(2);
    uint64_t covered[MAXW];
    memset(covered, 0, sizeof(covered));
    static int chosen[MAXD];
    int nc = 0;
    for (int k = 0; k < dd; k++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < N; s++) {
            if (col[s] != 1 - c) continue;
            int used = 0;
            for (int q = 0; q < nc; q++)
                if (chosen[q] == s) { used = 1; break; }
            if (used) continue;
            const uint64_t *row = b + (size_t)s * nw;
            int g = 0;
            for (int w = 0; w < nw; w++) g += popc64(row[w] & ~covered[w]);
            long sc = (long)g * 4096 + rndint(4096);
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        const uint64_t *row = b + (size_t)best * nw;
        for (int w = 0; w < nw; w++) covered[w] |= row[w];
    }
    int v = N;
    N++;
    col[v] = c;
    deg[v] = 0;
    for (int q = 0; q < nc; q++) {
        int s = chosen[q];
        if (deg[s] >= dd) {
            int j = rndint(deg[s]);
            int t = adjv[s][j];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

static void save_best(void) {
    bestN = N;
    bestM = 0;
    for (int v = 0; v < N; v++) {
        for (int j = 0; j < deg[v]; j++) {
            int u = adjv[v][j];
            if (v < u && bestM < MAXE) {
                bestU[bestM] = v;
                bestV[bestM] = u;
                bestM++;
            }
        }
    }
    bestValid = 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    double tl = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (dd < 1 || dd > MAXD || DD < 2 || n < 1 || n > MAXN - 256 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (deg[u] >= dd || deg[v] >= dd || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    if (ok) {
        static int q[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int x = q[qh++];
                for (int j = 0; j < deg[x]; j++) {
                    int y = adjv[x][j];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        q[qt++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                        break;
                    }
                }
                if (!ok) break;
            }
        }
    }
    if (!ok) { printf("0 0\n"); return 0; }

    double t0 = (double)clock() / CLOCKS_PER_SEC;
    double deadline = t0 + tl;

    rebuild_side0();
    fill_edges();
    long cur = cost_now();
    int ep = 0;
    unsigned long it = 0;

    for (;;) {
        if ((it & 127u) == 0 && (double)clock() / CLOCKS_PER_SEC >= deadline) break;
        it++;
        if (cur == 0) {
            save_best();
            if (N + 2 >= MAXN) break;
            add_vertex();
            rebuild_side0();
            fill_edges();
            cur = cost_now();
            ep = 0;
            continue;
        }
        if (n0 < 2) break;
        double T = THI * pow(TLO / THI, (double)ep / EPOCH);
        if (++ep >= EPOCH) {
            ep = 0;
            fill_edges();
            cur = cost_now();
            continue;
        }
        int a = side0[rndint(n0)];
        if (deg[a] == 0) continue;
        int b = adjv[a][rndint(deg[a])];
        int c = side0[rndint(n0)];
        if (c == a || deg[c] == 0) continue;
        int e = adjv[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost_now();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    if (cur == 0) save_best();
    if (!bestValid) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starting graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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
# Python helpers for growth and twin duplication.
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
# C annealing stage.
# ----------------------------------------------------------------------------

def _c_refine(n, edges, d, D, seed, end):
    """Run the C annealer from (n, edges) until monotonic time `end`. Returns valid (n, edges) or None."""
    tmo = end - time.monotonic() - 0.3
    if tmo < 3.0:
        return None
    budget = tmo - 1.5
    try:
        text = lib.run_c(C_SOURCE, [d, D, int(seed) % 1000000007, f"{budget:.2f}"],
                         stdin_graph=(n, edges), timeout=tmo)
        n2, e2 = lib.parse_graph_text(text)
    except Exception:
        return None
    if lib.is_valid(n2, e2, d, D):
        return n2, e2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
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
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * T, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * T
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C bitset annealer with vertex insertion, started from the best valid graph so far.
    if D >= 2:
        out = _c_refine(best_n, best_e, d, D, seed, start + 0.88 * T)
        if out is not None:
            consider(out[0], out[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
