import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 8000
#define MAXD 64
#define WN ((MAXN + 63) / 64)

static int N, DD, DIAM;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int color[MAXN];

static int bN;
static int bdeg[MAXN];
static int badj[MAXN][MAXD];
static int bcolor[MAXN];

static uint64_t ballB[MAXN][WN];
static uint64_t ballF[MAXN][WN];
static uint64_t tmpb[MAXN][WN];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int nwords(void) { return (N + 63) / 64; }

static double now_sec(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static void compute_balls(int r, uint64_t (*out)[WN]) {
    int nw = nwords();
    uint64_t (*cur)[WN] = out;
    uint64_t (*nx)[WN] = tmpb;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) nx[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < nw; w++) nx[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[WN] = cur;
        cur = nx;
        nx = t;
    }
    if (cur != out) {
        for (int v = 0; v < N; v++)
            for (int w = 0; w < nw; w++) out[v][w] = cur[v][w];
    }
}

static int all_full(uint64_t (*B)[WN]) {
    int nw = nwords();
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += popc(B[v][w]);
        if (c != N) return 0;
    }
    return 1;
}

/* Randomized greedy cover of all N vertices by at most DD vertices of side `side`
   with spare degree. Returns the number chosen, or 0 on failure. */
static int cover_side(int side, uint64_t (*B)[WN], int *chosen) {
    static uint64_t cov[WN], full[WN];
    static int cands[MAXN], gain[MAXN];
    static char used[MAXN];
    int nw = nwords();
    int nca = 0;
    for (int v = 0; v < N; v++) {
        if (color[v] == side && deg[v] < DD) {
            cands[nca++] = v;
            used[v] = 0;
        }
    }
    for (int i = nca - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = cands[i];
        cands[i] = cands[j];
        cands[j] = t;
    }
    for (int w = 0; w < nw; w++) {
        cov[w] = 0;
        full[w] = 0;
    }
    for (int v = 0; v < N; v++) full[v >> 6] |= 1ULL << (v & 63);
    int nc = 0;
    while (nc < DD) {
        int done = 1;
        for (int w = 0; w < nw; w++) {
            if (cov[w] != full[w]) {
                done = 0;
                break;
            }
        }
        if (done) break;
        int maxg = 0;
        for (int i = 0; i < nca; i++) {
            int c = cands[i];
            if (used[c]) {
                gain[i] = -1;
                continue;
            }
            int g = 0;
            for (int w = 0; w < nw; w++) g += popc(B[c][w] & ~cov[w]);
            gain[i] = g;
            if (g > maxg) maxg = g;
        }
        if (maxg == 0) break;
        int thr = maxg;
        if (maxg > 1 && rndi(10) < 3) thr = maxg - 1;
        int pick = -1, cnt = 0;
        for (int i = 0; i < nca; i++) {
            if (gain[i] >= thr && gain[i] > 0) {
                cnt++;
                if (rndi(cnt) == 0) pick = i;
            }
        }
        if (pick < 0) break;
        int c = cands[pick];
        used[c] = 1;
        chosen[nc++] = c;
        for (int w = 0; w < nw; w++) cov[w] |= B[c][w];
    }
    for (int w = 0; w < nw; w++) {
        if (cov[w] != full[w]) return 0;
    }
    return nc;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void remove_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][--deg[a]];
            break;
        }
    }
    for (int k = 0; k < deg[b]; k++) {
        if (adj[b][k] == a) {
            adj[b][k] = adj[b][--deg[b]];
            break;
        }
    }
}

/* Add edges between deficient opposite-side vertices (never breaks diameter). */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DD) {
            if (color[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = L[i];
        L[i] = L[j];
        L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = R[i];
        R[i] = R[j];
        R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < DD; j++) {
            int b = R[j];
            if (deg[b] < DD && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void save_state(void) {
    bN = N;
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(badj, adj, sizeof(adj[0]) * (size_t)N);
    memcpy(bcolor, color, sizeof(int) * (size_t)N);
}

static void restore_state(void) {
    N = bN;
    memcpy(deg, bdeg, sizeof(int) * (size_t)N);
    memcpy(adj, badj, sizeof(adj[0]) * (size_t)N);
    memcpy(color, bcolor, sizeof(int) * (size_t)N);
}

/* One move: optionally sacrifice edges at saturated vertices, add a cover vertex,
   re-saturate, and keep the result only if the whole graph still has diameter <= DIAM. */
static int step(void) {
    if (N + 2 >= MAXN) return 0;
    save_state();
    int side = rndi(2);
    if (rndi(2) == 0) {
        static int sat[MAXN];
        int ns = 0;
        for (int v = 0; v < N; v++)
            if (color[v] == side && deg[v] == DD) sat[ns++] = v;
        if (ns > 0) {
            int t = 1 + rndi(3);
            for (int i = 0; i < t && ns > 0; i++) {
                int j = rndi(ns);
                int s = sat[j];
                sat[j] = sat[--ns];
                if (deg[s] == 0) continue;
                int y = adj[s][rndi(deg[s])];
                remove_edge(s, y);
            }
        }
    }
    compute_balls(DIAM - 1, ballB);
    int chosen[MAXD];
    int k = cover_side(side, ballB, chosen);
    if (k <= 0) {
        restore_state();
        return 0;
    }
    int v = N++;
    color[v] = 1 - side;
    deg[v] = 0;
    for (int i = 0; i < k; i++) add_edge(chosen[i], v);
    saturate();
    compute_balls(DIAM, ballF);
    if (!all_full(ballF)) {
        restore_state();
        return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    double t0 = now_sec();
    if (DD < 1 || DD > MAXD - 4 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    if (n > MAXN / 2) {
        printf("0 0\n");
        return 0;
    }
    if (n <= 0) {
        N = 2;
        color[0] = 0;
        color[1] = 1;
        deg[0] = deg[1] = 0;
        add_edge(0, 1);
    } else {
        N = n;
        for (int v = 0; v < N; v++) {
            deg[v] = 0;
            color[v] = -1;
        }
        for (int i = 0; i < m; i++) {
            int a, b;
            if (scanf("%d %d", &a, &b) != 2) break;
            if (a < 0 || b < 0 || a >= N || b >= N || a == b) continue;
            if (deg[a] >= DD || deg[b] >= DD || has_edge(a, b)) continue;
            add_edge(a, b);
        }
        static int q[MAXN];
        for (int s = 0; s < N; s++) {
            if (color[s] >= 0) continue;
            color[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = adj[u][k];
                    if (color[w] < 0) {
                        color[w] = 1 - color[u];
                        q[qt++] = w;
                    } else if (color[w] == color[u]) {
                        printf("0 0\n");
                        return 0;
                    }
                }
            }
        }
    }
    /* The start graph must be valid, otherwise report nothing. */
    compute_balls(DIAM, ballF);
    if (!all_full(ballF)) {
        printf("0 0\n");
        return 0;
    }
    double end = t0 + tl;
    while (now_sec() < end) {
        step();
    }
    int tot = 0;
    for (int v = 0; v < N; v++) tot += deg[v];
    printf("%d %d\n", N, tot / 2);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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


def _gq_qs(d, count):
    """Largest prime powers q (q <= 16, q + 1 <= d), up to `count` of them, largest first."""
    return [q for q in range(d - 1, 1, -1) if q <= 16 and lib.is_prime_power(q)][:count]


# ----------------------------------------------------------------------------
# Python-side growth (cover extension + saturation), used before the C engine.
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
    """Greedy set cover of `full` by at most d candidate vertices, or None."""
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover all vertices (diameter preserved)."""
    if D < 2:
        return n, edges
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


def _grow(n, edges, d, D, deadline, rng):
    """Cover-extend first, then saturate edges with spare degree. Diameter is preserved."""
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    py_deadline = start + 0.3 * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Algebraic bases: PG(2, q) for D = 3, W(q) for D >= 4 (two largest usable q).
    bases = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        bases = [(lambda q=q: lib.projective_plane_incidence(q)) for q in qs]
    elif D >= 4:
        qs = _gq_qs(d, 2)
        bases = [(lambda q=q: _gq_w(q)) for q in qs]

    if bases:
        t0 = time.monotonic()
        span = max(0.0, py_deadline - t0)
        for i, make in enumerate(bases):
            gn, ge = make()
            consider(gn, ge)
            slice_end = t0 + span * (i + 1) / len(bases)
            n2, e2 = _grow(gn, ge, d, D, slice_end, rng)
            consider(n2, e2)

    # C engine: starts from the best Python graph and searches for larger valid graphs.
    if D >= 2 and d <= 60 and 0 < best_n < 4000:
        budget = deadline - time.monotonic() - 1.5
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=best, timeout=budget + 5.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
