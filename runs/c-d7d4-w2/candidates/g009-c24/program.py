import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXD 16
#define WMAX ((MAXN + 63) / 64)

static int N, D_, d_;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t rs = 88172645463325252ULL;
static uint64_t BG[MAXN][WMAX];

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static State SNAP, BESTS;

static uint64_t rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int m) { return (int)(rnd() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void save_state(State *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof deg);
    memcpy(s->adj, adj, sizeof adj);
    memcpy(s->col, col, sizeof col);
}

static void load_state(const State *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof deg);
    memcpy(adj, s->adj, sizeof adj);
    memcpy(col, s->col, sizeof col);
}

/* Bitset ball of radius r for every vertex; result written to out. */
static void compute_ball(int r, uint64_t (*out)[WMAX]) {
    int W = (N + 63) >> 6;
    static uint64_t tmp[MAXN][WMAX];
    uint64_t (*cu)[WMAX] = out, (*nx)[WMAX] = tmp;
    for (int v = 0; v < N; v++) {
        memset(cu[v], 0, sizeof(uint64_t) * W);
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = cu[v][w];
                for (int k = 0; k < deg[v]; k++) x |= cu[adj[v][k]][w];
                nx[v][w] = x;
                if (x != cu[v][w]) changed = 1;
            }
        }
        uint64_t (*t)[WMAX] = cu;
        cu = nx;
        nx = t;
        if (!changed) break;
    }
    if (cu != out) memcpy(out, cu, sizeof(uint64_t) * WMAX * N);
}

/* Number of unordered vertex pairs at distance > D_. */
static int bad_pairs(void) {
    compute_ball(D_, BG);
    int W = (N + 63) >> 6;
    long long reach = 0;
    for (int v = 0; v < N; v++)
        for (int w = 0; w < W; w++) reach += popc(BG[v][w]);
    long long bad = (long long)N * N - reach;
    return (int)(bad / 2);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) return 1;
    return 0;
}

static void del_from(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adj[a][k] == b) {
            adj[a][k] = adj[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void del_edge(int a, int b) {
    del_from(a, b);
    del_from(b, a);
}

static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}

static void shuffle_ints(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices. Never increases bad pairs. */
static void fill_edges(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_ints(L, nl);
    shuffle_ints(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/*
 * Cover insertion: a new vertex v on side 1-s is joined to a greedy set of
 * side-s vertices whose radius-(D-1) balls cover the graph. Full neighbours
 * give up one random edge (the repair step fixes the damage).
 */
static int add_cover_vertex(void) {
    static uint64_t Bc[MAXN][WMAX];
    if (N + 1 >= MAXN) return -1;
    int s = rndint(2);
    compute_ball(D_ - 1, Bc);
    int W = (N + 63) >> 6;
    uint64_t cov[WMAX];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    for (int pick = 0; pick < d_; pick++) {
        int bc = -1, bg = 0;
        double bs = -1.0;
        for (int c = 0; c < N; c++) {
            if (col[c] != s) continue;
            int used = 0;
            for (int i = 0; i < nc; i++)
                if (chosen[i] == c) { used = 1; break; }
            if (used) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(Bc[c][w] & ~cov[w]);
            double sc = g + 0.5 * rndu();
            if (sc > bs) { bs = sc; bc = c; bg = g; }
        }
        if (bc < 0 || bg == 0) break;
        chosen[nc++] = bc;
        for (int w = 0; w < W; w++) cov[w] |= Bc[bc][w];
    }
    int v = N++;
    col[v] = 1 - s;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= d_) {
            int t = adj[c][rndint(deg[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
    return v;
}

/* Delete vertex x; the last vertex is moved into slot x. */
static void remove_vertex(int x) {
    for (int k = 0; k < deg[x]; k++) del_from(adj[x][k], x);
    deg[x] = 0;
    int L = N - 1;
    if (x != L) {
        for (int k = 0; k < deg[L]; k++) {
            int u = adj[L][k];
            for (int j = 0; j < deg[u]; j++) {
                if (adj[u][j] == L) { adj[u][j] = x; break; }
            }
        }
        memcpy(adj[x], adj[L], sizeof(adj[L]));
        deg[x] = deg[L];
        col[x] = col[L];
    }
    N = L;
}

static int random_side(int side) {
    for (int t = 0; t < 4000; t++) {
        int v = rndint(N);
        if (col[v] == side && deg[v] > 0) return v;
    }
    return -1;
}

/*
 * Simulated annealing over bipartite double-edge switches (degrees and
 * bipartition preserved) plus cross-edge fills. Returns the final bad-pair count.
 */
static int anneal(int iters, double T0, double T1, double tlimit) {
    int cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now() > tlimit) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (rndu() < 0.1) {
            int x = rndint(N);
            if (deg[x] < d_) {
                for (int t = 0; t < 30; t++) {
                    int y = rndint(N);
                    if (col[y] != col[x] && deg[y] < d_ && !has_edge(x, y)) {
                        add_edge(x, y);
                        cur = bad_pairs();
                        break;
                    }
                }
            }
            continue;
        }
        int a = random_side(0);
        if (a < 0) break;
        int c = random_side(0);
        if (c < 0 || c == a) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        int nw = bad_pairs();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur;
}

static void make_kdd(void) {
    memset(deg, 0, sizeof deg);
    N = 2 * d_;
    for (int v = 0; v < N; v++) col[v] = (v < d_) ? 0 : 1;
    for (int i = 0; i < d_; i++)
        for (int j = 0; j < d_; j++) add_edge(i, d_ + j);
}

/* Read "n m" and edges from stdin. Returns 0 if absent or invalid. */
static int load_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 < 2 || n0 > MAXN - 200 || m0 < 0) return 0;
    memset(deg, 0, sizeof deg);
    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) return 0;
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    static int stk[MAXN];
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d_ < 1 || d_ > MAXD || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    if (!load_input()) make_kdd();
    fill_edges();
    if (bad_pairs() != 0) {
        anneal(2000, 0.5, 0.02, t0 + budget);
    }
    if (bad_pairs() != 0) make_kdd();

    save_state(&BESTS);
    save_state(&SNAP);

    while (now() - t0 < budget) {
        double r = rndu();
        int kill = ((r < 0.08 && N > 12) || N + 2 >= MAXN);
        if (!kill) {
            add_cover_vertex();
        } else {
            int k = 1 + rndint(3);
            for (int i = 0; i < k && N > 4; i++) remove_vertex(rndint(N));
        }
        fill_edges();
        int cst = anneal(kill ? 400 : 800, 1.0, 0.05, t0 + budget);
        if (cst == 0) {
            if (N > BESTS.n) save_state(&BESTS);
            if (N + 2 >= BESTS.n) {
                save_state(&SNAP);
            } else {
                load_state(&BESTS);
                save_state(&SNAP);
            }
        } else {
            load_state(&SNAP);
        }
    }

    State *b = &BESTS;
    int m = 0;
    for (int v = 0; v < b->n; v++)
        for (int k = 0; k < b->deg[v]; k++)
            if (v < b->adj[v][k]) m++;
    printf("%d %d\n", b->n, m);
    for (int v = 0; v < b->n; v++)
        for (int k = 0; k < b->deg[v]; k++)
            if (v < b->adj[v][k]) printf("%d %d\n", v, b->adj[v][k]);
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d (q limited to keep Python fast)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Structured start: W(q) for D >= 4, PG(2,q) for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None and base[0] <= 1000 and lib.is_valid(base[0], base[1], d, D):
        if base[0] > best[0]:
            best = base
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Let the C engine grow the start graph (cover insertion, repair, kill-and-regrow).
    elapsed = time.monotonic() - t_start
    budget = 0.85 * time_limit - elapsed - 1.0
    if budget >= 2.0 and 1 <= d <= 15 and D >= 2:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best,
                            timeout=0.95 * time_limit - (time.monotonic() - t_start))
            n2, e2 = lib.parse_graph_text(out)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], list(best[1])
