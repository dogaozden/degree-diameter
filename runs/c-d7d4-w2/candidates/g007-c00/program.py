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

#define MAXN 1280
#define WMAX 20
#define MAXD 24

static int d_, D_;
static int n_;
static int deg_[MAXN];
static int adj_[MAXN][MAXD];
static int col_[MAXN];
static uint64_t bufA[MAXN][WMAX];
static uint64_t bufB[MAXN][WMAX];
static uint64_t rs_ = 88172645463325252ULL;

static int best_ok = 0;
static int best_n = 0;
static int best_deg[MAXN];
static int best_adj[MAXN][MAXD];
static int best_col[MAXN];

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static uint64_t rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int has_edge(int a, int b) {
    for (int i = 0; i < deg_[a]; i++)
        if (adj_[a][i] == b) return 1;
    return 0;
}
static void del_arc(int a, int b) {
    for (int i = 0; i < deg_[a]; i++) {
        if (adj_[a][i] == b) {
            adj_[a][i] = adj_[a][--deg_[a]];
            return;
        }
    }
}
static void remove_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}
static void add_edge(int a, int b) {
    adj_[a][deg_[a]++] = b;
    adj_[b][deg_[b]++] = a;
}

static int pc64(uint64_t x) {
    int c = 0;
    while (x) {
        x &= x - 1;
        c++;
    }
    return c;
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long cost(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) bufA[v][w] = 0;
        bufA[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = bufA[v][w];
                for (int i = 0; i < deg_[v]; i++) x |= bufA[adj_[v][i]][w];
                bufB[v][w] = x;
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) bufA[v][w] = bufB[v][w];
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(bufA[v][w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static void save_best(void) {
    best_n = n_;
    memcpy(best_deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(best_adj, adj_, sizeof(adj_));
    memcpy(best_col, col_, sizeof(int) * (size_t)n_);
    best_ok = 1;
}

static void load_best(void) {
    n_ = best_n;
    memcpy(deg_, best_deg, sizeof(int) * (size_t)best_n);
    memcpy(adj_, best_adj, sizeof(adj_));
    memcpy(col_, best_col, sizeof(int) * (size_t)best_n);
}

/* Insert a new vertex pair x (colour 0), y (colour 1) by d double-edge switches:
   remove a-b, add x-b and a-y. Degrees of old vertices are unchanged. */
static int insert_pair(void) {
    if (n_ + 2 > MAXN) return 0;
    int x = n_, y = n_ + 1;
    n_ += 2;
    deg_[x] = 0;
    deg_[y] = 0;
    col_[x] = 0;
    col_[y] = 1;
    int done = 0;
    long tries = 0;
    while (done < d_ && tries < 200000) {
        tries++;
        int a = rndint(n_ - 2);
        if (col_[a] != 0 || deg_[a] == 0) continue;
        int b = adj_[a][rndint(deg_[a])];
        if (has_edge(x, b) || has_edge(a, y)) continue;
        remove_edge(a, b);
        add_edge(x, b);
        add_edge(a, y);
        done++;
    }
    if (deg_[x] < d_ && deg_[y] < d_ && !has_edge(x, y)) add_edge(x, y);
    return 1;
}

/* Pick a double-edge switch a-b, c-e -> a-e, c-b between colour-0 a,c and colour-1 b,e. */
static int pick_switch(int *pa, int *pb, int *pc, int *pe) {
    for (int tr = 0; tr < 100; tr++) {
        int A = rndint(n_);
        if (col_[A] != 0 || deg_[A] == 0) continue;
        int B = adj_[A][rndint(deg_[A])];
        int C = rndint(n_);
        if (col_[C] != 0 || C == A || deg_[C] == 0) continue;
        int E = adj_[C][rndint(deg_[C])];
        if (B == E) continue;
        if (has_edge(A, E) || has_edge(C, B)) continue;
        *pa = A;
        *pb = B;
        *pc = C;
        *pe = E;
        return 1;
    }
    return 0;
}
static void do_switch(int a, int b, int c, int e) {
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}
static void undo_switch(int a, int b, int c, int e) {
    remove_edge(a, e);
    remove_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static void perturb(int k) {
    for (int t = 0; t < k; t++) {
        int a, b, c, e;
        if (!pick_switch(&a, &b, &c, &e)) return;
        do_switch(a, b, c, e);
    }
}

/* Anneal over degree-preserving switches to minimise bad pairs. Returns final cost. */
static long anneal(long iters, double deadline) {
    long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now_s() > deadline) break;
        int a, b, c, e;
        if (!pick_switch(&a, &b, &c, &e)) break;
        do_switch(a, b, c, e);
        long nw = cost();
        int accept;
        if (nw <= cur) accept = 1;
        else if (nw == cur + 1) accept = rnd01() < 0.05;
        else accept = rnd01() < 0.002;
        if (accept) cur = nw;
        else undo_switch(a, b, c, e);
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs_ ^= seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double deadline = now_s() + tl;

    if (d_ < 1 || d_ > MAXD - 1 || D_ < 1 || D_ > 50) {
        printf("0 0\n");
        return 0;
    }
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN - 2) {
        printf("0 0\n");
        return 0;
    }
    n_ = n;
    memset(deg_, 0, sizeof(deg_));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (has_edge(u, v)) continue;
        if (deg_[u] >= d_ || deg_[v] >= d_) continue;
        add_edge(u, v);
    }

    /* Two-colour the input (BFS). */
    for (int v = 0; v < n; v++) col_[v] = -1;
    int *queue = (int *)malloc(sizeof(int) * MAXN);
    for (int s = 0; s < n; s++) {
        if (col_[s] != -1) continue;
        col_[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg_[u]; i++) {
                int v = adj_[u][i];
                if (col_[v] == -1) {
                    col_[v] = 1 - col_[u];
                    queue[qt++] = v;
                }
            }
        }
    }
    free(queue);

    if (cost() == 0) {
        save_best();
    } else {
        anneal(3000, deadline);
        if (cost() == 0) save_best();
    }

    while (best_ok && now_s() < deadline) {
        load_best();
        perturb(2 + rndint(4));
        if (!insert_pair()) break;
        long c = anneal(1500, deadline);
        if (c == 0) save_best();
    }

    if (!best_ok) {
        printf("0 0\n");
        return 0;
    }
    int total = 0;
    for (int v = 0; v < best_n; v++) total += best_deg[v];
    printf("%d %d\n", best_n, total / 2);
    for (int v = 0; v < best_n; v++) {
        for (int i = 0; i < best_deg[v]; i++) {
            int u = best_adj[v][i];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions
# ----------------------------------------------------------------------------

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
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python glue
# ----------------------------------------------------------------------------

def _color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _saturate(n, edges, d, rng):
    """Add cross-side edges between deficient vertices. Distances only shrink, so validity holds."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _color(n, adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    out = list(edges)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            out.append((a, b))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)

    # Safe fallback: K_{d,d} (diameter 2).
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 1, []

    # Structured start: generalized quadrangle for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        e0 = _saturate(n0, e0, d, rng)
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best_n, best_e = n0, e0

    # Calibration cases already at the Moore bound: return instantly.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Pair insertion with degree-preserving annealing, run in C.
    elapsed = time.monotonic() - t0
    remaining = time_limit * 0.75 - elapsed - 1.0
    if d <= 20 and remaining > 3:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining * 0.85, 2)],
                            stdin_graph=(best_n, best_e), timeout=remaining + 4)
            n1, e1 = lib.parse_graph_text(out)
            if n1 > best_n and lib.is_valid(n1, e1, d, D):
                best_n, best_e = n1, e1
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
