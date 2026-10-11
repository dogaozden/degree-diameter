import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 64
#define MAXW 32
#define ITERS 20000L

typedef uint64_t u64;

static int n = 0, d = 0, D = 0, nw = 1;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];

static int sn = 0;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];

static u64 bufA[MAXN][MAXW];
static u64 bufB[MAXN][MAXW];
static unsigned char pc16[65536];
static u64 rs = 88172645463325252ULL;
static double budget_sec = 1.0;
static int queue_buf[MAXN];

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(rnd64() % (u64)k); }

static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int timeup(void) { return (double)clock() / (double)CLOCKS_PER_SEC >= budget_sec; }

static int popw(u64 x) {
    return pc16[x & 0xFFFFu] + pc16[(x >> 16) & 0xFFFFu] +
           pc16[(x >> 32) & 0xFFFFu] + pc16[(x >> 48) & 0xFFFFu];
}

/* Number of unordered vertex pairs at distance greater than D. */
static long cost(void) {
    u64 (*cur)[MAXW] = bufA;
    u64 (*nxt)[MAXW] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int step = 0; step < D; step++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) {
                u64 x = cur[v][w];
                for (int k = 0; k < deg[v]; k++) x |= cur[adj[v][k]][w];
                nxt[v][w] = x;
            }
        }
        u64 (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < nw; w++) tot += popw(cur[v][w]);
    return ((long)n * n - tot) / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void drop_one(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void remove_edge(int a, int b) {
    drop_one(a, b);
    drop_one(b, a);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void save_state(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(sadj, adj, sizeof(int) * (size_t)n * MAXD);
    memcpy(scol, col, sizeof(int) * (size_t)n);
}

static void restore_state(void) {
    n = sn;
    nw = (n + 63) / 64;
    memcpy(deg, sdeg, sizeof(int) * (size_t)n);
    memcpy(adj, sadj, sizeof(int) * (size_t)n * MAXD);
    memcpy(col, scol, sizeof(int) * (size_t)n);
}

static int color_graph(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue_buf[qt++] = s;
        while (qh < qt) {
            int u = queue_buf[qh++];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    queue_buf[qt++] = w;
                }
            }
        }
    }
    for (int u = 0; u < n; u++)
        for (int k = 0; k < deg[u]; k++)
            if (col[adj[u][k]] == col[u]) return 0;
    return 1;
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add one vertex on a random side, joined to d opposite-side vertices:
   deficient ones first, then saturated ones, freeing one edge at each. */
static void add_vertex(void) {
    static int defs[MAXN], full[MAXN];
    int c = rnd(2), want = 1 - c;
    int nd = 0, nf = 0;
    for (int u = 0; u < n; u++) {
        if (col[u] != want) continue;
        if (deg[u] < d) defs[nd++] = u;
        else full[nf++] = u;
    }
    shuffle(defs, nd);
    shuffle(full, nf);
    int v = n;
    n++;
    nw = (n + 63) / 64;
    col[v] = c;
    deg[v] = 0;
    int taken = 0;
    for (int i = 0; i < nd && taken < d; i++) {
        add_edge(v, defs[i]);
        taken++;
    }
    for (int i = 0; i < nf && taken < d; i++) {
        int s = full[i];
        int t = adj[s][rnd(deg[s])];
        remove_edge(s, t);
        add_edge(v, s);
        taken++;
    }
}

/* Adding edges never increases distances, so this only helps. */
static void fill_edges(void) {
    long tries = 8L * n;
    for (long t = 0; t < tries; t++) {
        int a = rnd(n), b = rnd(n);
        if (col[a] != 0 || col[b] != 1) continue;
        if (deg[a] >= d || deg[b] >= d) continue;
        if (has_edge(a, b)) continue;
        add_edge(a, b);
    }
}

/* Bipartite double-edge switches (degrees and sides preserved) annealing the bad-pair cost.
   Returns 1 if cost reaches 0. */
static int anneal(long iters) {
    long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 127) == 0 && timeup()) break;
        double frac = (double)it / (double)iters;
        double T = 1.5 * (1.0 - frac) + 0.03;
        int a = rnd(n);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = adj[a][rnd(deg[a])];
        int c = rnd(n);
        if (col[c] != 0 || c == a || deg[c] == 0) continue;
        int e = adj[c][rnd(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long nc = cost();
        long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

static void print_snapshot(void) {
    long cnt = 0;
    for (int v = 0; v < sn; v++)
        for (int k = 0; k < sdeg[v]; k++)
            if (sadj[v][k] > v) cnt++;
    printf("%d %ld\n", sn, cnt);
    for (int v = 0; v < sn; v++)
        for (int k = 0; k < sdeg[v]; k++)
            if (sadj[v][k] > v) printf("%d %d\n", v, sadj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget_sec = atof(argv[4]);
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int i = 1; i < 65536; i++) pc16[i] = (unsigned char)(pc16[i >> 1] + (i & 1));

    int m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n < 1 || n > MAXN - 64 || d < 1 || d > MAXD || D < 1 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    if (!color_graph()) {
        printf("0 0\n");
        return 0;
    }
    nw = (n + 63) / 64;
    if (!anneal(ITERS * 4)) {
        printf("0 0\n");
        return 0;
    }
    save_state();
    while (!timeup()) {
        restore_state();
        if (n >= MAXN - 2) break;
        add_vertex();
        fill_edges();
        if (anneal(ITERS)) save_state();
    }
    print_snapshot();
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            grow_end = t0 + 0.15 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Native stage: C annealer adds vertices one at a time, repairing with bipartite
    # switches. Skipped when the graph already meets the Moore bound (calibration cases).
    moore = lib.moore_bound(d, D)
    if D >= 3 and d >= 3 and d <= 60 and best_n < moore:
        c_deadline = t0 + 0.85 * time_limit
        budget = c_deadline - time.monotonic() - 1.5
        if budget > 1.0:
            timeout = max(2.0, c_deadline + 0.05 * time_limit - time.monotonic())
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=(best_n, best_e), timeout=timeout)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
