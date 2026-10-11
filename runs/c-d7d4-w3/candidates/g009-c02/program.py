import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite degree-bounded annealing with incremental vertex insertion.
#
# State: bipartite graph with max degree d (side 0 = edge tail, side 1 = head).
# Cost = number of vertex pairs at distance > D, computed with bitset balls.
# Moves: degree-preserving edge switches (Metropolis), greedy edge additions.
# Growth: insert a new vertex pair (a on side 0, b on side 1) by a degree-preserving
# split of d disjoint edges. Each growth is followed by annealing to cost 0.
# Best valid graph is kept and printed. Starts from a given graph or K_{d,d}.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXE (MAXN * MAXD / 2 + 64)
#define WM (MAXN / 64 + 2)

static int d, D;
static int N, M, capN;
static int side[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXD];
static unsigned char mat[MAXN][MAXN];
static int ea[MAXE], eb[MAXE];
static uint64_t bufA[MAXN][WM], bufB[MAXN][WM];
static uint64_t rs;

typedef struct {
    int n, m;
    int side[MAXN];
    int ea[MAXE], eb[MAXE];
} Snap;
static Snap snapA, bestS;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static void replace_nb(int x, int oldv, int newv) {
    for (int k = 0; k < deg[x]; k++)
        if (nb[x][k] == oldv) { nb[x][k] = newv; return; }
}

static void add_edge(int a, int b) {
    mat[a][b] = mat[b][a] = 1;
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
    ea[M] = a;
    eb[M] = b;
    M++;
}

/* Rebuild adjacency and matrix from ea/eb; returns 0 on duplicate edge or degree overflow. */
static int rebuild(void) {
    memset(mat, 0, sizeof(mat));
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) {
        int a = ea[i], b = eb[i];
        if (a == b || mat[a][b]) return 0;
        if (deg[a] >= d || deg[b] >= d) return 0;
        mat[a][b] = mat[b][a] = 1;
        nb[a][deg[a]++] = b;
        nb[b][deg[b]++] = a;
    }
    return 1;
}

static void snap_save(Snap *s) {
    s->n = N;
    s->m = M;
    memcpy(s->side, side, sizeof(int) * N);
    memcpy(s->ea, ea, sizeof(int) * M);
    memcpy(s->eb, eb, sizeof(int) * M);
}

static void snap_load(const Snap *s) {
    N = s->n;
    M = s->m;
    memcpy(side, s->side, sizeof(int) * N);
    memcpy(ea, s->ea, sizeof(int) * M);
    memcpy(eb, s->eb, sizeof(int) * M);
    rebuild();
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > D (unreachable counts). */
static long cost(void) {
    int W = (N + 63) >> 6;
    uint64_t (*cu)[WM] = bufA;
    uint64_t (*nx)[WM] = bufB;
    for (int v = 0; v < N; v++) {
        for (int w = 0; w < W; w++) cu[v][w] = 0;
        cu[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < W; w++) nx[v][w] = cu[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) nx[v][w] |= cu[u][w];
            }
        }
        uint64_t (*t)[WM] = cu;
        cu = nx;
        nx = t;
    }
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cu[v][w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Edge i = (A,B), edge j = (C,E) become (A,E), (C,B). Involution: applying twice undoes. */
static void do_switch(int i, int j) {
    int A = ea[i], B = eb[i], C = ea[j], E = eb[j];
    mat[A][B] = mat[B][A] = 0;
    mat[C][E] = mat[E][C] = 0;
    mat[A][E] = mat[E][A] = 1;
    mat[C][B] = mat[B][C] = 1;
    replace_nb(A, B, E);
    replace_nb(B, A, C);
    replace_nb(C, E, B);
    replace_nb(E, C, A);
    eb[i] = E;
    eb[j] = B;
}

static void greedy_fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (side[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    for (int i = n0 - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = L0[i]; L0[i] = L0[j]; L0[j] = t;
    }
    for (int i = n1 - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = L1[i]; L1[i] = L1[j]; L1[j] = t;
    }
    for (int i = 0; i < n0; i++)
        for (int j = 0; j < n1; j++) {
            int a = L0[i], b = L1[j];
            if (M < MAXE && deg[a] < d && deg[b] < d && !mat[a][b]) add_edge(a, b);
        }
}

/* Insert new pair (a side 0, b side 1) by splitting d disjoint edges. Degree-preserving for others. */
static int insert_pair(void) {
    if (N + 2 > capN || M + d > MAXE) return 0;
    int idx[MAXD], xs[MAXD], ys[MAXD], k = 0;
    for (int t = 0; t < 80 * d && k < d; t++) {
        int i = rndi(M);
        int x = ea[i], y = eb[i], ok = 1;
        for (int q = 0; q < k; q++)
            if (xs[q] == x || ys[q] == y) { ok = 0; break; }
        if (ok) {
            idx[k] = i;
            xs[k] = x;
            ys[k] = y;
            k++;
        }
    }
    if (k < d) return 0;
    int a = N++, b = N++;
    side[a] = 0;
    side[b] = 1;
    deg[a] = 0;
    deg[b] = 0;
    for (int q = 0; q < k; q++) {
        int i = idx[q], x = xs[q], y = ys[q];
        mat[x][y] = mat[y][x] = 0;
        mat[a][y] = mat[y][a] = 1;
        mat[x][b] = mat[b][x] = 1;
        replace_nb(x, y, b);
        replace_nb(y, x, a);
        nb[a][deg[a]++] = y;
        nb[b][deg[b]++] = x;
        ea[i] = a;
        eb[i] = y;
        ea[M] = x;
        eb[M] = b;
        M++;
    }
    return 1;
}

static void try_record(long c) {
    if (c == 0 && N > bestS.n) snap_save(&bestS);
}

static int read_input(void) {
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) return 0;
    if (n0 <= 0 || n0 > capN || m0 <= 0 || m0 > MAXE) return 0;
    static int ru[MAXE], rv[MAXE];
    static int head[MAXN], col[MAXN], stk[MAXN];
    static int nxt[2 * MAXE], to[2 * MAXE];
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &ru[i], &rv[i]) != 2) return 0;
        if (ru[i] < 0 || ru[i] >= n0 || rv[i] < 0 || rv[i] >= n0 || ru[i] == rv[i]) return 0;
    }
    for (int v = 0; v < n0; v++) { head[v] = -1; col[v] = -1; }
    for (int i = 0; i < m0; i++) {
        int h = 2 * i;
        to[h] = rv[i];
        nxt[h] = head[ru[i]];
        head[ru[i]] = h;
        h = 2 * i + 1;
        to[h] = ru[i];
        nxt[h] = head[rv[i]];
        head[rv[i]] = h;
    }
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int h = head[u]; h >= 0; h = nxt[h]) {
                int v = to[h];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    stk[sp++] = v;
                } else if (col[v] == col[u]) {
                    return 0;
                }
            }
        }
    }
    N = n0;
    M = 0;
    for (int v = 0; v < N; v++) side[v] = col[v];
    for (int i = 0; i < m0; i++) {
        if (col[ru[i]] == 0) { ea[M] = ru[i]; eb[M] = rv[i]; }
        else { ea[M] = rv[i]; eb[M] = ru[i]; }
        M++;
    }
    return rebuild();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double mb = 0, pw = 1;
    for (int i = 0; i < D; i++) { mb += pw; pw *= (d - 1); }
    capN = (int)(2.0 * mb + 0.5);
    if (capN > MAXN) capN = MAXN;

    double t_start = now();
    double t_end = t_start + tl;

    if (!read_input()) {
        N = 2 * d;
        M = 0;
        for (int v = 0; v < N; v++) side[v] = (v < d) ? 0 : 1;
        for (int i = 0; i < d; i++)
            for (int j = 0; j < d; j++) {
                ea[M] = i;
                eb[M] = d + j;
                M++;
            }
        rebuild();
    }
    greedy_fill();
    long cur = cost();
    try_record(cur);

    int has_snap = 0;
    if (cur == 0) {
        snap_save(&snapA);
        has_snap = 1;
    }

    while (now() < t_end) {
        if (cur == 0) {
            try_record(0);
            snap_save(&snapA);
            has_snap = 1;
            if (N + 2 > capN || M + d > MAXE) break;
            if (!insert_pair()) continue;
            cur = cost();
        }
        int K = 2000 + 8 * N;
        for (int s = 0; s < K && cur > 0; s++) {
            if ((s & 63) == 0 && now() >= t_end) break;
            double frac = (double)s / K;
            double T = 1.5 * pow(0.08 / 1.5, frac);
            if (rndu() < 0.15) {
                int v1 = rndi(N), v2 = rndi(N);
                if (side[v1] != side[v2]) {
                    int a = (side[v1] == 0) ? v1 : v2;
                    int b = (side[v1] == 0) ? v2 : v1;
                    if (M < MAXE && deg[a] < d && deg[b] < d && !mat[a][b]) {
                        add_edge(a, b);
                        cur = cost();
                    }
                }
                continue;
            }
            int i = rndi(M), j = rndi(M);
            if (i == j) continue;
            int a = ea[i], b = eb[i], c = ea[j], e = eb[j];
            if (a == c || b == e || mat[a][e] || mat[c][b]) continue;
            do_switch(i, j);
            long nc = cost();
            if (nc <= cur || rndu() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                do_switch(i, j);
            }
        }
        if (cur != 0 && has_snap) {
            snap_load(&snapA);
            cur = 0;
        }
    }

    try_record(cur);
    printf("%d %d\n", bestS.n, bestS.m);
    for (int i = 0; i < bestS.m; i++) printf("%d %d\n", bestS.ea[i], bestS.eb[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _pg_base(d):
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


def _gq_base(d):
    """W(q) incidence graph for the largest prime power q <= 16 with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Driver: structured base (diameter-matched), then C annealing growth.
# Every returned graph passes lib.is_valid; K_{d,d} / Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    def result():
        return best_n, list(best_e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # C_{2D}: Moore graph for d = 2
        return result()
    if d > 16 or d < 3:
        return result()

    moore = lib.moore_bound(d, D)

    base = None
    if D == 3:
        base = _pg_base(d)
    elif D == 4:
        base = _gq_base(d)
    if base is not None:
        consider(*base)
    if best_n >= moore:
        return result()

    elapsed = time.monotonic() - t0
    remaining = 0.92 * time_limit - elapsed
    c_budget = remaining - 1.5
    if c_budget < 1.0:
        return result()

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                         stdin_graph=(best_n, best_e), timeout=remaining)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except (RuntimeError, ValueError, OSError):
        pass
    return result()
