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

#define MAXN 2048
#define MAXD 40
#define MAXW (MAXN / 64)

static int N, DD, DIAM, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int side[MAXN];

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Snap;

static Snap CUR;
static uint64_t BUF0[MAXN][MAXW];
static uint64_t BUF1[MAXN][MAXW];

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static double TLIM = 10.0;

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
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
    for (int k = 0; k < deg[a]; k++)
        if (adj[a][k] == b) { adj[a][k] = adj[a][--deg[a]]; break; }
    for (int k = 0; k < deg[b]; k++)
        if (adj[b][k] == a) { adj[b][k] = adj[b][--deg[b]]; break; }
}

/* Bitset balls of given radius: out[v] = set of vertices within `rounds` steps of v. */
static void balls(int rounds, uint64_t (*out)[MAXW]) {
    static uint64_t tmp[MAXN][MAXW];
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        memset(out[v], 0, sizeof(uint64_t) * MAXW);
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < rounds; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) tmp[v][w] = out[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) tmp[v][w] |= out[u][w];
            }
        }
        for (int v = 0; v < N; v++)
            for (int w = 0; w < W; w++) out[v][w] = tmp[v][w];
    }
}

/* Number of unordered pairs at distance > DIAM (unreachable counted). */
static int cost_eval(void) {
    balls(DIAM, BUF0);
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(BUF0[v][w]);
        unr += N - c;
    }
    return (int)(unr / 2);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (never increases distances). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DD) {
            if (side[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < DD; j++) {
            int b = R[j];
            if (deg[b] < DD && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex joined to a greedy radius-(DIAM-1) cover; steal slots where needed. */
static int grow_vertex(void) {
    if (N + 1 >= MAXN) return 0;
    int c = rndi(2);
    int opp = 1 - c;
    balls(DIAM - 1, BUF1);
    static int used[MAXN];
    static int chosen[MAXD];
    memset(used, 0, sizeof(int) * N);
    uint64_t covered[MAXW];
    memset(covered, 0, sizeof covered);
    int nch = 0;
    for (int t = 0; t < DD; t++) {
        int best = -1;
        long long bestscore = -1;
        for (int s = 0; s < N; s++) {
            if (side[s] != opp || used[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pc64(BUF1[s][w] & ~covered[w]);
            long long sc = (long long)g * 4 + (deg[s] < DD ? 3 : 0) + rndi(3);
            if (sc > bestscore) { bestscore = sc; best = s; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) covered[w] |= BUF1[best][w];
    }
    if (nch == 0) return 0;
    int v = N;
    side[v] = c;
    deg[v] = 0;
    N++;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg[s] >= DD) {
            int t = adj[s][rndi(deg[s])];
            remove_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

/* Annealing with bipartite switches and degree-shifting moves; returns 1 if cost reaches 0. */
static int anneal(long long iters, double T0, double T1) {
    fill();
    int cur = cost_eval();
    if (cur == 0) return 1;
    static int S0[MAXN], S1[MAXN], DF[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (side[v] == 0) S0[n0++] = v;
        else S1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) return cur == 0;
    double lr = log(T1 / T0);
    for (long long it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && elapsed() > TLIM) break;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int mv = rndi(10);
        if (mv < 8) {
            int a = S0[rndi(n0)];
            int c = S0[rndi(n0)];
            if (a == c || deg[a] == 0 || deg[c] == 0) continue;
            int b = adj[a][rndi(deg[a])];
            int e = adj[c][rndi(deg[c])];
            if (has_edge(a, e) || has_edge(c, b)) continue;
            remove_edge(a, b);
            remove_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            int nw = cost_eval();
            if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                remove_edge(a, e);
                remove_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else {
            int nd = 0;
            for (int i = 0; i < n1; i++)
                if (deg[S1[i]] < DD) DF[nd++] = S1[i];
            if (nd == 0) continue;
            int e = DF[rndi(nd)];
            int a = S0[rndi(n0)];
            if (deg[a] == 0 || has_edge(a, e)) continue;
            int b = adj[a][rndi(deg[a])];
            remove_edge(a, b);
            add_edge(a, e);
            int nw = cost_eval();
            if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                remove_edge(a, e);
                add_edge(a, b);
            }
        }
    }
    return cur == 0;
}

static void save_snap(Snap *s) {
    s->n = N;
    for (int v = 0; v < N; v++) {
        s->deg[v] = deg[v];
        memcpy(s->adj[v], adj[v], sizeof(int) * deg[v]);
    }
}

static void load_snap(const Snap *s) {
    N = s->n;
    for (int v = 0; v < N; v++) {
        deg[v] = s->deg[v];
        memcpy(adj[v], s->adj[v], sizeof(int) * deg[v]);
    }
}

static void build_kdd(int d) {
    N = 2 * d;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int v = 0; v < N; v++) side[v] = (v < d) ? 0 : 1;
    for (int a = 0; a < d; a++)
        for (int b = d; b < 2 * d; b++)
            add_edge(a, b);
}

static int read_input(void) {
    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0 || n > MAXN - 200) return 0;
    N = n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= DD || deg[v] >= DD || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    static int q[MAXN];
    for (int s = 0; s < N; s++) side[s] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt) {
            int x = q[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (side[y] < 0) {
                    side[y] = 1 - side[x];
                    q[qt++] = y;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    TLIM = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (DD < 1 || DD >= MAXD || DIAM < 2) {
        printf("1 0\n");
        return 0;
    }
    if (!read_input()) build_kdd(DD);

    if (cost_eval() != 0) anneal(200000, 1.5, 0.1);
    if (cost_eval() != 0) build_kdd(DD);
    save_snap(&CUR);

    while (elapsed() < TLIM) {
        load_snap(&CUR);
        if (!grow_vertex()) break;
        long long iters = 3000 + 12LL * N;
        if (anneal(iters, 1.2, 0.08)) {
            save_snap(&CUR);
        }
    }

    load_snap(&CUR);
    int E = 0;
    for (int v = 0; v < N; v++) E += deg[v];
    E /= 2;
    printf("%d %d\n", N, E);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = adj[v][k];
            if (v < u) printf("%d %d\n", v, u);
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
    """Generalized quadrangle incidence graph W(q), q + 1 <= d, q small enough for Python."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    # Structured base: W(q) for D >= 4, PG(2,q) for D = 3.
    if D == 2:
        base = None
    elif D == 3:
        base = _best_pg(d)
    else:
        base = _best_gq(d)
    if base is not None:
        n0, e0 = base
        if n0 > best_n and lib.is_valid(n0, e0, d, D):
            best_n, best_e = n0, list(e0)
            if best_n == lib.moore_bound(d, D):
                return best_n, list(best_e)

    # Bold stage: C engine grows the base by annealed vertex insertion.
    if D >= 2 and best_n > 0:
        elapsed = time.monotonic() - t0
        cbudget = max(1.0, 0.75 * time_limit - elapsed)
        timeout = max(cbudget + 3.0, 0.9 * time_limit - elapsed)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                            stdin_graph=(best_n, best_e), timeout=timeout)
            n1, e1 = lib.parse_graph_text(out)
            if n1 > best_n and lib.is_valid(n1, e1, d, D):
                best_n, best_e = n1, list(e1)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
