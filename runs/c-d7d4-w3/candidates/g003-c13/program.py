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
#define MAXD 40
#define MAXW (MAXN / 64)
#define GROW_IT 1500

static int d_, D_, n_;
static int adj_[MAXN][MAXD], deg_[MAXN], col_[MAXN];
static int sadj_[MAXN][MAXD], sdeg_[MAXN], scol_[MAXN], sn_;
static int bestn_ = 0, bestm_ = 0;
static int bestE_[MAXN * MAXD][2];
static uint64_t ball_[MAXN][MAXW], tmp_[MAXN][MAXW];
static int W_;
static unsigned char pc_[65536];
static uint64_t rs_ = 88172645463325252ULL;
static clock_t endc_;

static uint64_t nxt(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rnd(int k) { return (int)(nxt() % (uint64_t)k); }
static double rndf(void) { return (double)(nxt() >> 11) * (1.0 / 9007199254740992.0); }

static inline int popc(uint64_t x) {
    return pc_[x & 0xffff] + pc_[(x >> 16) & 0xffff] + pc_[(x >> 32) & 0xffff] + pc_[(x >> 48) & 0xffff];
}

static int find_slot(int v, int u) {
    for (int k = 0; k < deg_[v]; k++)
        if (adj_[v][k] == u) return k;
    return -1;
}
static void repl(int v, int old, int nw) {
    int k = find_slot(v, old);
    adj_[v][k] = nw;
}
static int has_edge(int a, int b) { return find_slot(a, b) >= 0; }
static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}
static void remove_edge(int a, int b) {
    int k = find_slot(a, b);
    adj_[a][k] = adj_[a][--deg_[a]];
    k = find_slot(b, a);
    adj_[b][k] = adj_[b][--deg_[b]];
}

static int color_all(void) {
    static int stack[MAXN];
    for (int v = 0; v < n_; v++) col_[v] = -1;
    for (int s = 0; s < n_; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int sp = 0;
        stack[sp++] = s;
        while (sp) {
            int u = stack[--sp];
            for (int k = 0; k < deg_[u]; k++) {
                int v = adj_[u][k];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    stack[sp++] = v;
                } else if (col_[v] == col_[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void compute_balls(int r) {
    int n = n_;
    W_ = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W_; w++) ball_[v][w] = 0;
        ball_[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W_; w++) tmp_[v][w] = ball_[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                int u = adj_[v][k];
                for (int w = 0; w < W_; w++) tmp_[v][w] |= ball_[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W_; w++) ball_[v][w] = tmp_[v][w];
    }
}

static long cost_(int r) {
    compute_balls(r);
    long bad = 0;
    for (int v = 0; v < n_; v++) {
        int c = 0;
        for (int w = 0; w < W_; w++) c += popc(ball_[v][w]);
        bad += n_ - c;
    }
    return bad / 2;
}

static void fill_(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] >= d_) continue;
        if (col_[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr; j++) {
            if (deg_[a] >= d_) break;
            int b = R[j];
            if (deg_[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void add_vertex(int side) {
    int n = n_;
    compute_balls(D_ - 1);
    uint64_t cov[MAXW];
    for (int w = 0; w < W_; w++) cov[w] = 0;
    char used[MAXN];
    for (int s = 0; s < n; s++) used[s] = 0;
    int chosen[MAXD];
    int nc = 0;
    for (int step = 0; step < d_; step++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < n; s++) {
            if (col_[s] != side || used[s]) continue;
            int g = 0;
            for (int w = 0; w < W_; w++) g += popc(ball_[s][w] & ~cov[w]);
            long sc = (long)g * 1024 + rnd(1024);
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0 || bs / 1024 == 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W_; w++) cov[w] |= ball_[best][w];
    }
    int v = n_++;
    col_[v] = 1 - side;
    deg_[v] = 0;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg_[s] >= d_) {
            int t = adj_[s][rnd(deg_[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
}

static void kill_vertex(int x) {
    for (int k = 0; k < deg_[x]; k++) {
        int t = adj_[x][k];
        int s = find_slot(t, x);
        adj_[t][s] = adj_[t][--deg_[t]];
    }
    deg_[x] = 0;
    int last = n_ - 1;
    if (x != last) {
        for (int k = 0; k < deg_[last]; k++) repl(adj_[last][k], last, x);
        memcpy(adj_[x], adj_[last], sizeof(int) * MAXD);
        deg_[x] = deg_[last];
        col_[x] = col_[last];
    }
    n_--;
}

static long anneal_(long iters, double T) {
    long cur = cost_(D_);
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && clock() > endc_) break;
        int n = n_;
        int a = rnd(n);
        if (col_[a] != 0 || deg_[a] == 0) continue;
        int b = adj_[a][rnd(deg_[a])];
        int c = rnd(n);
        if (col_[c] != 0 || c == a || deg_[c] == 0) continue;
        int e = adj_[c][rnd(deg_[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        repl(a, b, e);
        repl(e, c, a);
        repl(c, e, b);
        repl(b, a, c);
        long nw = cost_(D_);
        long delta = nw - cur;
        if (delta <= 0 || (T > 0 && rndf() < exp(-(double)delta / T))) {
            cur = nw;
        } else {
            repl(a, e, b);
            repl(b, c, a);
            repl(c, b, e);
            repl(e, a, c);
        }
    }
    return cur;
}

static void snap_save(void) {
    sn_ = n_;
    memcpy(sadj_, adj_, sizeof(int) * MAXD * n_);
    memcpy(sdeg_, deg_, sizeof(int) * n_);
    memcpy(scol_, col_, sizeof(int) * n_);
}
static void snap_load(void) {
    n_ = sn_;
    memcpy(adj_, sadj_, sizeof(int) * MAXD * n_);
    memcpy(deg_, sdeg_, sizeof(int) * n_);
    memcpy(col_, scol_, sizeof(int) * n_);
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n_; u++)
        for (int k = 0; k < deg_[u]; k++) {
            int v = adj_[u][k];
            if (u < v) {
                bestE_[m][0] = u;
                bestE_[m][1] = v;
                m++;
            }
        }
    bestm_ = m;
    bestn_ = n_;
}

static void load_graph(int n, int m, int E[][2]) {
    n_ = n;
    for (int v = 0; v < n; v++) deg_[v] = 0;
    for (int i = 0; i < m; i++) add_edge(E[i][0], E[i][1]);
    color_all();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs_ ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    double tl = atof(argv[4]);
    for (int i = 0; i < 65536; i++) pc_[i] = (unsigned char)(pc_[i >> 1] + (i & 1));
    endc_ = clock() + (clock_t)(tl * CLOCKS_PER_SEC);

    int n0 = 0, m0 = 0;
    if (d_ < 1 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 8 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    n_ = n0;
    for (int v = 0; v < n0; v++) deg_[v] = 0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v ||
            deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    if (!ok || !color_all()) { printf("0 0\n"); return 0; }

    int alive = 1;
    if (cost_(D_) == 0) {
        save_best();
    } else {
        if (anneal_(400000, 0.3) != 0) alive = 0;
        else save_best();
    }

    while (alive && clock() < endc_) {
        if (bestn_ > 0 && n_ + 3 < bestn_) load_graph(bestn_, bestm_, bestE_);
        if (n_ + 2 >= MAXN) break;
        snap_save();
        add_vertex(rnd(2));
        fill_();
        long c = anneal_(GROW_IT, 0.35);
        if (c == 0) {
            if (n_ > bestn_) save_best();
        } else {
            snap_load();
            if (rnd(100) < 25) {
                kill_vertex(rnd(n_));
                fill_();
                if (anneal_(GROW_IT / 2, 0.25) != 0) snap_load();
            }
        }
    }

    if (bestn_ <= 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestn_, bestm_);
    for (int i = 0; i < bestm_; i++) printf("%d %d\n", bestE_[i][0], bestE_[i][1]);
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


# ----------------------------------------------------------------------------
# Python helpers: cheap growth of the structured base before the C search.
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

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.1 * time_limit, rng)
            consider(n1, e1)

    # C engine: annealed vertex addition with bitset-based diameter cost,
    # starting from the best valid graph found in Python.
    if D >= 2 and d <= 40:
        elapsed = time.monotonic() - start
        cbudget = 0.72 * time_limit - elapsed
        if cbudget >= 1.0:
            timeout = 0.92 * time_limit - elapsed
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{cbudget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=timeout)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
