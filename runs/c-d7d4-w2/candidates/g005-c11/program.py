import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define WMAX 32

typedef uint64_t Row[WMAX];

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

typedef struct { int a, b, c, e; } Sw;

static int N = 0, NW = 1, DG = 3, DIA = 3;
static int deg_[MAXN];
static int adj_[MAXN][MAXD];
static int col_[MAXN];
static Row BALL[MAXN];
static Row COVER[MAXN];
static Row TMP[MAXN];
static State SNAP_PRE, SNAP_BEST;
static uint64_t rs = 88172645463325252ULL;
static clock_t deadline;
static unsigned char pc16[65536];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return clock() >= deadline; }

static void init_pc(void) {
    for (int i = 1; i < 65536; i++) pc16[i] = (unsigned char)(pc16[i >> 1] + (i & 1));
}
static int popc64(uint64_t x) {
    return pc16[x & 0xFFFF] + pc16[(x >> 16) & 0xFFFF] +
           pc16[(x >> 32) & 0xFFFF] + pc16[(x >> 48) & 0xFFFF];
}
static void setN(int n) {
    N = n;
    NW = (n + 63) >> 6;
    if (NW < 1) NW = 1;
}
static int popcount_row(const uint64_t *r) {
    int c = 0;
    for (int w = 0; w < NW; w++) c += popc64(r[w]);
    return c;
}
static int has_edge(int u, int v) {
    for (int k = 0; k < deg_[u]; k++)
        if (adj_[u][k] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj_[u][deg_[u]++] = v;
    adj_[v][deg_[v]++] = u;
}
static void rem_from(int u, int v) {
    for (int k = 0; k < deg_[u]; k++) {
        if (adj_[u][k] == v) {
            adj_[u][k] = adj_[u][--deg_[u]];
            return;
        }
    }
}
static void del_edge(int u, int v) {
    rem_from(u, v);
    rem_from(v, u);
}

/* out[v] = bitmask of vertices within distance r of v */
static void balls(int r, Row *out) {
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(uint64_t) * NW);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            memcpy(TMP[v], out[v], sizeof(uint64_t) * NW);
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *x = out[adj_[v][k]];
                for (int w = 0; w < NW; w++) TMP[v][w] |= x[w];
            }
        }
        for (int v = 0; v < N; v++) memcpy(out[v], TMP[v], sizeof(uint64_t) * NW);
    }
}

/* number of unordered pairs at distance > DIA (unreachable counts) */
static long cost(void) {
    balls(DIA, BALL);
    long bad = 0;
    for (int v = 0; v < N; v++) bad += (long)(N - popcount_row(BALL[v]));
    return bad / 2;
}

static int random_vertex_side(int side) {
    for (int t = 0; t < 1000; t++) {
        int v = rndi(N);
        if (col_[v] == side && deg_[v] > 0) return v;
    }
    return -1;
}

/* degree-preserving bipartite double-edge switch on two side-0 vertices */
static int try_switch(Sw *s) {
    int a = random_vertex_side(0);
    int c = random_vertex_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj_[a][rndi(deg_[a])];
    int e = adj_[c][rndi(deg_[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    s->a = a; s->b = b; s->c = c; s->e = e;
    return 1;
}

static void undo_switch(const Sw *s) {
    del_edge(s->a, s->e);
    del_edge(s->c, s->b);
    add_edge(s->a, s->b);
    add_edge(s->c, s->e);
}

static void shuffle_arr(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* add cross-side edges between deficient vertices (never hurts distances) */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg_[v] < DG) {
            if (col_[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle_arr(L0, n0);
    shuffle_arr(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg_[a] < DG; j++) {
            int b = L1[j];
            if (deg_[b] < DG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void remove_vertex(int x) {
    while (deg_[x] > 0) del_edge(x, adj_[x][0]);
    int L = N - 1;
    if (x != L) {
        deg_[x] = deg_[L];
        col_[x] = col_[L];
        for (int k = 0; k < deg_[L]; k++) adj_[x][k] = adj_[L][k];
        for (int k = 0; k < deg_[x]; k++) {
            int u = adj_[x][k];
            for (int j = 0; j < deg_[u]; j++)
                if (adj_[u][j] == L) adj_[u][j] = x;
        }
    }
    deg_[L] = 0;
    setN(N - 1);
}

/* COVER must hold balls of radius DIA-1 for the current graph */
static void add_vertex(int side) {
    int chosen[MAXD];
    int nc = 0;
    Row cov;
    memset(cov, 0, sizeof(uint64_t) * NW);
    for (int it = 0; it < DG; it++) {
        if (popcount_row(cov) >= N) break;
        int best = -1;
        long bs = -1;
        for (int s = 0; s < N; s++) {
            if (col_[s] != side) continue;
            int used = 0;
            for (int j = 0; j < nc; j++)
                if (chosen[j] == s) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < NW; w++) g += popc64(COVER[s][w] & ~cov[w]);
            long sc = (long)g * 4096 + rndi(4096);
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (int w = 0; w < NW; w++) cov[w] |= COVER[best][w];
    }
    int v = N;
    setN(N + 1);
    deg_[v] = 0;
    col_[v] = 1 - side;
    for (int j = 0; j < nc; j++) {
        int s = chosen[j];
        if (deg_[s] >= DG) {
            int t = adj_[s][rndi(deg_[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

/* delete the worst vertices until the graph is valid */
static int repair(void) {
    long c = cost();
    while (c > 0) {
        if (timeup() || N <= 2) return 0;
        balls(DIA, BALL);
        int worst = 0;
        long bs = -1;
        for (int v = 0; v < N; v++) {
            long bad = (long)(N - popcount_row(BALL[v]));
            long sc = bad * 4096 + rndi(4096);
            if (sc > bs) { bs = sc; worst = v; }
        }
        remove_vertex(worst);
        fill();
        c = cost();
    }
    return 1;
}

static void save(State *s) {
    s->n = N;
    memcpy(s->deg, deg_, sizeof(deg_));
    memcpy(s->adj, adj_, sizeof(adj_));
    memcpy(s->col, col_, sizeof(col_));
}

static void load(const State *s) {
    setN(s->n);
    memcpy(deg_, s->deg, sizeof(deg_));
    memcpy(adj_, s->adj, sizeof(adj_));
    memcpy(col_, s->col, sizeof(col_));
}

static int anneal(long iters) {
    long cur = cost();
    if (cur == 0) return 1;
    const double T0 = 1.2, T1 = 0.05;
    for (long it = 0; it < iters; it++) {
        if ((it & 31) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        Sw sw;
        if (!try_switch(&sw)) continue;
        long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_switch(&sw);
        }
    }
    return cur == 0;
}

static void output_state(const State *s) {
    int m = 0;
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->adj[v][k] > v) m++;
    printf("%d %d\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++)
            if (s->adj[v][k] > v) printf("%d %d\n", v, s->adj[v][k]);
}

static int read_graph(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 0 || n > MAXN || m < 0) return 0;
    setN(n);
    for (int v = 0; v < n; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg_[u] >= DG || deg_[v] >= DG || has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++) col_[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adj_[u][k];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    stk[sp++] = v;
                } else if (col_[v] == col_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DG = atoi(argv[1]);
    DIA = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 100; i++) rnd();
    init_pc();
    clock_t t0 = clock();
    deadline = t0 + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    if (DG < 2 || DG > MAXD || DIA < 2 || DIA > 60) { printf("0 0\n"); return 0; }
    if (!read_graph() || N < 2) { printf("0 0\n"); return 0; }
    if (!repair()) { printf("0 0\n"); return 0; }
    fill();
    if (cost() != 0) { printf("0 0\n"); return 0; }
    save(&SNAP_BEST);

    while (!timeup()) {
        /* neutral walk on the valid graph */
        for (int t = 0; t < 16; t++) {
            Sw sw;
            if (!try_switch(&sw)) continue;
            if (cost() != 0) undo_switch(&sw);
        }
        if (N + 1 >= MAXN) break;
        save(&SNAP_PRE);
        int side = rndi(2);
        balls(DIA - 1, COVER);
        add_vertex(side);
        fill();
        if (anneal(1000)) save(&SNAP_BEST);
        else load(&SNAP_PRE);
    }
    output_state(&SNAP_BEST);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are 0..P-1, lines are P..2P-1; degree q+1, diameter 4.
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """PG(2, q) incidence for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _matching_free(n, edges, rng):
    """Delete a random perfect matching from a regular bipartite graph (left = 0..n/2-1).

    Returns (n, edges) with degree one less, or None if no perfect matching is found.
    """
    half = n // 2
    adj = [[] for _ in range(half)]
    for u, v in edges:
        a, b = min(u, v), max(u, v)
        adj[a].append(b - half)
    match_r = [-1] * half

    def augment(u, seen):
        for j in adj[u]:
            if j in seen:
                continue
            seen.add(j)
            if match_r[j] == -1 or augment(match_r[j], seen):
                match_r[j] = u
                return True
        return False

    order = list(range(half))
    rng.shuffle(order)
    for u in order:
        if not augment(u, set()):
            return None
    drop = {(match_r[j], j) for j in range(half)}
    out = []
    for u, v in edges:
        a, b = min(u, v), max(u, v)
        if (a, b - half) not in drop:
            out.append((a, b))
    return n, out


def _alt_base(d, D, rng):
    """Alternative construction: (d+1)-regular incidence structure minus a perfect matching."""
    if d < 3 or not lib.is_prime_power(d):
        return None
    if D == 4 and d <= 8:
        base = _gq_w(d)
    elif D == 3:
        base = lib.projective_plane_incidence(d)
    else:
        return None
    return _matching_free(base[0], base[1], rng)


# ----------------------------------------------------------------------------
# Python growth (cover vertices + edge saturation), kept as a cheap candidate.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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
            for attempt in range(100):
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
    """Join deficient opposite-side vertices. Only shortens distances, so validity is kept."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
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
# Build: structured bases, Python growth, then the C engine on two starts:
#   (a) the alternative base W(d) / PG(2,d) minus a perfect matching, repaired in C;
#   (b) the best valid graph so far, grown further in C.
# Every candidate is checked with lib.is_valid; the K_{d,d} fallback is always kept.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D < 2 or d < 3:
        return best_n, list(best_e)

    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    def run_engine(graph, budget, salt):
        if budget < 1.0:
            return
        try:
            text = lib.run_c(
                C_SOURCE,
                [d, D, (int(seed) * 1000003 + salt) & 0x7FFFFFFF, f"{budget:.2f}"],
                stdin_graph=graph,
                timeout=budget + 5.0,
            )
            n, e = lib.parse_graph_text(text)
        except Exception:
            return
        consider(n, e)

    alt = _alt_base(d, D, rng)
    if alt is not None and time.monotonic() < deadline - 2.0:
        run_engine(alt, 0.5 * (deadline - time.monotonic()) - 0.5, 1)

    remaining = deadline - time.monotonic() - 0.5
    if remaining >= 1.0:
        run_engine((best_n, list(best_e)), remaining, 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
