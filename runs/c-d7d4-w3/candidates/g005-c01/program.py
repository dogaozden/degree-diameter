import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: degree-preserving vertex-pair insertion with annealing.
#
# Idea (new): grow a d-regular-ish bipartite graph one vertex PAIR at a time.
# A new pair (a on side 0, b on side 1) is inserted by deleting d disjoint
# edges x_i-y_i and joining a to all y_i and b to all x_i. Degrees and
# bipartiteness are preserved. The new state is then annealed with
# degree-preserving edge switches (a-b, c-e -> a-e, c-b) that minimise the
# number of vertex pairs at distance > D. A zero-cost state is a valid graph
# and is kept. A failed anneal rolls back to the last valid graph.
# Bit-parallel BFS balls make each cost evaluation cheap.
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

static int N, DD, dd, W;
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char A[MAXN][MAXN];
static int side[MAXN];
static int slist[2][MAXN];
static int scnt[2];
static int qu[MAXN];

static int gN, gs0, gs1;
static int gdeg[MAXN];
static int gnb[MAXN][MAXD];
static unsigned char GA[MAXN][MAXN];

static uint64_t RA[MAXN * MAXW];
static uint64_t RB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double t0 = 0.0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - t0; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DD (unreachable counts). */
static long long cost(void) {
    int w = W;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) {
        uint64_t *p = cur + (size_t)v * w;
        for (int k = 0; k < w; k++) p[k] = 0;
        p[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < DD; it++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * w;
            const uint64_t *s = cur + (size_t)v * w;
            for (int k = 0; k < w; k++) o[k] = s[k];
            for (int j = 0; j < deg[v]; j++) {
                const uint64_t *t = cur + (size_t)nb[v][j] * w;
                for (int k = 0; k < w; k++) o[k] |= t[k];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *p = cur + (size_t)v * w;
        for (int k = 0; k < w; k++) c += pc64(p[k]);
        bad += N - c;
    }
    return bad / 2;
}

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    A[u][v] = A[v][u] = 1;
}

static void del_edge(int u, int v) {
    for (int j = 0; j < deg[u]; j++) if (nb[u][j] == v) { nb[u][j] = nb[u][--deg[u]]; break; }
    for (int j = 0; j < deg[v]; j++) if (nb[v][j] == u) { nb[v][j] = nb[v][--deg[v]]; break; }
    A[u][v] = A[v][u] = 0;
}

static void replace_nb(int u, int old, int nw) {
    for (int j = 0; j < deg[u]; j++) if (nb[u][j] == old) { nb[u][j] = nw; return; }
}

/* Remove edges ab, ce; add ae, cb. a,c on side 0; b,e on side 1. */
static void sw(int a, int b, int c, int e) {
    replace_nb(a, b, e);
    replace_nb(b, a, c);
    replace_nb(c, e, b);
    replace_nb(e, c, a);
    A[a][b] = A[b][a] = 0;
    A[c][e] = A[e][c] = 0;
    A[a][e] = A[e][a] = 1;
    A[c][b] = A[b][c] = 1;
}

static int pick_side(int s) {
    if (scnt[s] == 0) return -1;
    for (int t = 0; t < 64; t++) {
        int v = slist[s][rndi(scnt[s])];
        if (deg[v] > 0) return v;
    }
    return -1;
}

/* Add random bipartite edges between deficient vertices. */
static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < dd) {
            if (side[v] == 0) L[nl++] = v; else R[nr++] = v;
        }
    }
    long long tries = 50LL * N * dd + 1000;
    for (long long t = 0; t < tries && nl > 0 && nr > 0; t++) {
        int a = L[rndi(nl)], b = R[rndi(nr)];
        if (deg[a] >= dd || deg[b] >= dd || A[a][b]) continue;
        add_edge(a, b);
    }
}

/* Degree-preserving insertion of a new vertex pair. */
static int insert_pair(void) {
    if (N + 2 > MAXN) return 0;
    int xs[MAXD], ys[MAXD];
    int k = 0;
    for (int t = 0; t < 4000 && k < dd; t++) {
        int x = pick_side(0);
        if (x < 0) break;
        int y = nb[x][rndi(deg[x])];
        int clash = 0;
        for (int j = 0; j < k; j++) if (xs[j] == x || ys[j] == y) { clash = 1; break; }
        if (clash) continue;
        xs[k] = x; ys[k] = y; k++;
    }
    if (k < dd) return 0;
    for (int j = 0; j < k; j++) del_edge(xs[j], ys[j]);
    int a = N, b = N + 1;
    N += 2;
    W = (N + 63) / 64;
    for (int i = 0; i < N; i++) {
        A[a][i] = A[i][a] = 0;
        A[b][i] = A[i][b] = 0;
    }
    deg[a] = 0; deg[b] = 0;
    side[a] = 0; side[b] = 1;
    slist[0][scnt[0]++] = a;
    slist[1][scnt[1]++] = b;
    for (int j = 0; j < k; j++) {
        add_edge(a, ys[j]);
        add_edge(b, xs[j]);
    }
    return 1;
}

static void save_good(void) {
    gN = N; gs0 = scnt[0]; gs1 = scnt[1];
    for (int i = 0; i < N; i++) {
        gdeg[i] = deg[i];
        memcpy(gnb[i], nb[i], sizeof(nb[i]));
        memcpy(GA[i], A[i], (size_t)N);
    }
}

static void load_good(void) {
    N = gN; W = (N + 63) / 64;
    scnt[0] = gs0; scnt[1] = gs1;
    for (int i = 0; i < N; i++) {
        deg[i] = gdeg[i];
        memcpy(nb[i], gnb[i], sizeof(nb[i]));
        memcpy(A[i], GA[i], (size_t)N);
    }
}

/* Simulated annealing on edge switches. Returns 1 if cost reaches 0. */
static int anneal(long long cur, long long iters, double T0, double T1, double lim) {
    if (cur == 0) return 1;
    double lr = log(T1 / T0);
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && elapsed() > lim) return 0;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int a = pick_side(0);
        int c = pick_side(0);
        if (a < 0 || c < 0 || a == c) continue;
        int b = nb[a][rndi(deg[a])];
        int e = nb[c][rndi(deg[c])];
        if (A[a][e] || A[c][b]) continue;
        sw(a, b, c, e);
        long long nw = cost();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            sw(a, e, c, b);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    double budget = atof(argv[4]);
    t0 = (double)clock() / CLOCKS_PER_SEC;
    if (dd < 1 || dd > MAXD || DD < 2) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 <= 0 || n0 > MAXN - 2) {
        /* default start: K_{dd,dd} */
        N = 2 * dd;
        for (int v = 0; v < N; v++) side[v] = v < dd ? 0 : 1;
        for (int i = 0; i < dd; i++)
            for (int j = dd; j < 2 * dd; j++) add_edge(i, j);
    } else {
        N = n0;
        for (int i = 0; i < m0; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
            if (A[u][v] || deg[u] >= dd || deg[v] >= dd) continue;
            add_edge(u, v);
        }
        for (int v = 0; v < N; v++) side[v] = -1;
        int bad = 0;
        for (int s = 0; s < N && !bad; s++) {
            if (side[s] != -1) continue;
            side[s] = 0;
            int h = 0, t = 0;
            qu[t++] = s;
            while (h < t && !bad) {
                int u = qu[h++];
                for (int j = 0; j < deg[u]; j++) {
                    int v = nb[u][j];
                    if (side[v] == -1) { side[v] = 1 - side[u]; qu[t++] = v; }
                    else if (side[v] == side[u]) { bad = 1; break; }
                }
            }
        }
        if (bad) { printf("0 0\n"); return 0; }
    }
    for (int v = 0; v < N; v++) slist[side[v]][scnt[side[v]]++] = v;
    W = (N + 63) / 64;

    double dl = budget * 0.9;
    saturate();
    long long c0 = cost();
    int have = 0;
    if (c0 == 0) {
        save_good();
        have = 1;
    } else if (anneal(c0, 60000, 2.0, 0.08, budget * 0.3)) {
        save_good();
        have = 1;
    }
    if (!have) { printf("0 0\n"); return 0; }

    long long iters = 20000;
    int fails = 0;
    while (elapsed() < dl) {
        if (!insert_pair()) {
            if (++fails > 200) break;
            continue;
        }
        long long cc = cost();
        if (anneal(cc, iters, 2.0, 0.08, dl)) {
            save_good();
            iters = 20000;
            fails = 0;
        } else {
            load_good();
            iters = iters + iters / 2;
            if (iters > 200000) iters = 200000;
        }
    }

    load_good();
    long long m = 0;
    for (int u = 0; u < N; u++) m += deg[u];
    m /= 2;
    printf("%d %lld\n", N, m);
    for (int u = 0; u < N; u++)
        for (int j = 0; j < deg[u]; j++) {
            int v = nb[u][j];
            if (u < v) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (structured bases).
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
    """Largest W(q) with q + 1 <= d and q <= 8 (keeps construction time small)."""
    for q in range(d - 1, 1, -1):
        if q <= 8 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: best valid structured base, then the C insertion/annealing engine.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, always valid for D >= 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    bases = []
    if D >= 4:
        g = _best_gq(d)
        if g is not None:
            bases.append(g)
    if D >= 3:
        g = _best_pg(d)
        if g is not None:
            bases.append(g)
    for n, e in bases:
        consider(n, e)

    if best_n < lib.moore_bound(d, D):
        spent = time.monotonic() - t_start
        budget = 0.8 * time_limit - spent - 1.5
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, list(best_e)
