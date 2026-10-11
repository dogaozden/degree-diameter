"""Search for large bipartite graphs with max degree d and diameter D.

Starting points: incidence graphs of generalized quadrangles W(q) (D >= 4), projective
planes and Araujo-Pardo-Lopez graphs (D = 3), and K_{d,d} as a safe fallback.

New in this version: a C engine that grows a valid graph one vertex at a time. A new vertex
is joined to a greedy cover of radius D-1 balls (the cover guarantees distance <= D to every
old vertex). The diameter defect is then repaired by simulated annealing over degree-preserving
bipartite double-edge switches. The cost is the exact number of vertex pairs at distance > D,
computed with bitsets. Saturating spare degree only adds cross-side edges, so validity is kept.
"""
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

#define MAXN 4096
#define MAXW 64
#define MAXD 64
#define MAXE (MAXN * MAXD / 2)
#define STAGE_IT 10000

typedef uint64_t u64;
typedef u64 Row[MAXW];

static int d, D, n;
static int nb[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static Row BUFA[MAXN], BUFB[MAXN];
static char used[MAXN];
static int shufL[MAXN], shufR[MAXN];

static int bn = 0, bm = 0;
static int bu[MAXE], bv[MAXE];
static int bcol[MAXN];

static u64 rs = 88172645463325252ULL;
static double tlim;
static clock_t t0;

static u64 rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnext() % (u64)k); }
static double rndf(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++)
        if (nb[a][k] == b) return 1;
    return 0;
}

static void del_arc(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (nb[a][k] == b) {
            nb[a][k] = nb[a][--deg[a]];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void del_edge(int a, int b) {
    del_arc(a, b);
    del_arc(b, a);
}

/* Bitmask of vertices within distance r of each vertex; returns the buffer holding them. */
static Row *balls(int r) {
    int W = (n + 63) >> 6;
    Row *cur = BUFA, *nxt = BUFB;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(Row));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = nb[v][k];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        Row *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    return cur;
}

/* Number of unordered pairs at distance > D (unreachable pairs included). */
static long long cost_full(void) {
    int W = (n + 63) >> 6;
    Row *b = balls(D);
    long long s = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(b[v][w]);
        s += n - c;
    }
    return s / 2;
}

static int verify(void) {
    for (int v = 0; v < n; v++) {
        if (deg[v] > d || (col[v] != 0 && col[v] != 1)) return 0;
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (u == v || u < 0 || u >= n || col[u] == col[v]) return 0;
            for (int j = 0; j < k; j++)
                if (nb[v][j] == u) return 0;
        }
    }
    return 1;
}

static int color_graph(void) {
    for (int v = 0; v < n; v++) col[v] = -1;
    int *st = (int *)malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = nb[u][k];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    st[sp++] = w;
                } else if (col[w] == col[u]) {
                    free(st);
                    return 0;
                }
            }
        }
    }
    free(st);
    return 1;
}

static void build_complete(void) {
    n = 2 * d;
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        col[v] = v < d ? 0 : 1;
    }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            add_edge(i, d + j);
}

static void save_complete_as_best(void) {
    bn = 2 * d;
    bm = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            bu[bm] = i;
            bv[bm] = d + j;
            bm++;
        }
    for (int v = 0; v < 2 * d; v++) bcol[v] = v < d ? 0 : 1;
}

static void save_best(void) {
    if (!verify()) return;
    int m = 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (v < u) {
                if (m >= MAXE) return;
                bu[m] = v;
                bv[m] = u;
                m++;
            }
        }
    bn = n;
    bm = m;
    memcpy(bcol, col, sizeof(int) * (size_t)n);
}

static void restore_best(void) {
    for (int v = 0; v < bn; v++) deg[v] = 0;
    n = bn;
    memcpy(col, bcol, sizeof(int) * (size_t)bn);
    for (int i = 0; i < bm; i++) add_edge(bu[i], bv[i]);
}

static void shuffle(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Greedy maximal addition of cross-side edges between deficient vertices. */
static void saturate(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] >= d) continue;
        if (col[v] == 0) shufL[nl++] = v;
        else shufR[nr++] = v;
    }
    shuffle(shufL, nl);
    shuffle(shufR, nr);
    for (int i = 0; i < nl; i++) {
        int a = shufL[i];
        for (int j = 0; j < nr && deg[a] < d; j++) {
            int b = shufR[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Append a vertex on side sv, joined to a randomized greedy cover of radius D-1 balls. */
static void add_vertex(int sv) {
    int W = (n + 63) >> 6;
    Row *b = balls(D - 1);
    Row cov;
    memset(cov, 0, sizeof(Row));
    for (int v = 0; v < n; v++) used[v] = 0;
    int chosen[MAXD];
    int nc = 0;
    for (int t = 0; t < d; t++) {
        int best = -1;
        double bk = -1.0;
        for (int c = 0; c < n; c++) {
            if (col[c] != 1 - sv || used[c]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(b[c][w] & ~cov[w]);
            if (g == 0) continue;
            double key = (double)g + 0.9 * rndf();
            if (key > bk) {
                bk = key;
                best = c;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        for (int w = 0; w < W; w++) cov[w] |= b[best][w];
    }
    int v = n++;
    col[v] = sv;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int c = chosen[i];
        if (deg[c] >= d) {
            int x = nb[c][rndi(deg[c])];
            del_edge(c, x);
        }
        add_edge(c, v);
    }
}

/* One random degree-preserving bipartite double-edge switch (unconditional). */
static void random_switch(void) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rndi(n);
        if (col[a] != 0 || deg[a] == 0) continue;
        int b = nb[a][rndi(deg[a])];
        int c = rndi(n);
        if (col[c] != 0 || deg[c] == 0 || c == a) continue;
        int e = nb[c][rndi(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        return;
    }
}

/* Simulated annealing on the bad-pair count. Returns the final cost (0 means valid). */
static long long sa_stage(long long maxit, double T0) {
    long long cur = cost_full();
    for (long long it = 0; it < maxit && cur > 0; it++) {
        if ((it & 255) == 0 && elapsed() > tlim) break;
        double T = T0 * (1.0 - (double)it / (double)maxit) + 0.03;
        int a, b, c, e;
        if (rndi(10) < 7) {
            /* Double-edge switch: (a,b),(c,e) -> (a,e),(c,b). */
            a = rndi(n);
            if (col[a] != 0 || deg[a] == 0) continue;
            b = nb[a][rndi(deg[a])];
            c = rndi(n);
            if (col[c] != 0 || deg[c] == 0 || c == a) continue;
            e = nb[c][rndi(deg[c])];
            if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
            del_edge(a, b);
            del_edge(c, e);
            add_edge(a, e);
            add_edge(c, b);
            long long nw = cost_full();
            if (nw <= cur || rndf() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                del_edge(a, e);
                del_edge(c, b);
                add_edge(a, b);
                add_edge(c, e);
            }
        } else {
            /* Rewire: (a,b) -> (a,e) with e a deficient vertex on side 1. */
            a = rndi(n);
            if (col[a] != 0 || deg[a] == 0) continue;
            b = nb[a][rndi(deg[a])];
            e = rndi(n);
            if (col[e] != 1 || deg[e] >= d || e == b || has_edge(a, e)) continue;
            del_edge(a, b);
            add_edge(a, e);
            long long nw = cost_full();
            if (nw <= cur || rndf() < exp(-(double)(nw - cur) / T)) {
                cur = nw;
            } else {
                del_edge(a, e);
                add_edge(a, b);
            }
        }
    }
    return cur;
}

static int read_and_load(int n0, int m0, int *eu, int *ev) {
    if (n0 < 2 || n0 > MAXN || m0 < 0 || m0 > MAXE) return 0;
    n = n0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) return 0;
        add_edge(u, v);
    }
    return color_graph();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tlim = atof(argv[4]);
    t0 = clock();

    if (d < 1 || d > MAXD || D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (m0 < 0 || m0 > MAXE) m0 = 0;
    int *eu = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int *ev = (int *)malloc(sizeof(int) * (size_t)(m0 + 1));
    int got = 0;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) break;
        got++;
    }

    int ok = (got == m0) && read_and_load(n0, m0, eu, ev);
    if (!ok) build_complete();

    saturate();
    long long cur = cost_full();

    bn = 0;
    bm = 0;
    if (cur == 0) save_best();
    if (bn == 0) save_complete_as_best();

    while (elapsed() < tlim) {
        if (cur == 0) {
            if (n > bn) save_best();
            if (n + 1 >= MAXN) break;
            add_vertex(rndi(2));
            saturate();
            cur = cost_full();
            continue;
        }
        cur = sa_stage(STAGE_IT, 1.2);
        if (cur > 0 && elapsed() < tlim) {
            restore_best();
            int k = 1 + rndi(6);
            for (int i = 0; i < k; i++) random_switch();
            cur = cost_full();
        }
    }
    if (cur == 0 && n > bn) save_best();

    printf("%d %d\n", bn, bm);
    for (int i = 0; i < bm; i++) printf("%d %d\n", bu[i], bv[i]);
    free(eu);
    free(ev);
    return 0;
}
"""


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _pp_below(limit, lo=2):
    """Largest prime power q with lo <= q <= limit, or None."""
    for q in range(limit, lo - 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _candidates(d, D):
    """Structured starting graphs for degree d and diameter D (K_{d,d} always included)."""
    cands = []
    if D >= 4:
        q = _pp_below(min(d - 1, 9))  # keep the pure-Python W(q) build fast
        if q is not None:
            cands.append(_gq_w(q))
    if D >= 3:
        q = _pp_below(d - 1)
        if q is not None:
            cands.append(lib.projective_plane_incidence(q))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    cands.append(lib.haar_graph(d, range(d)))
    return cands


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        m = 2 * D
        return m, [(i, (i + 1) % m) for i in range(m)]
    if d > 60:
        return lib.haar_graph(d, range(d))

    best_n, best_e = None, None
    for n, e in _candidates(d, D):
        if lib.is_valid(n, e, d, D) and (best_n is None or n > best_n):
            best_n, best_e = n, e

    budget = max(0.3, 0.72 * float(time_limit) - (time.monotonic() - t_start) - 0.5)
    try:
        text = lib.run_c(C_SOURCE, [d, D, int(seed), round(budget, 2)],
                         stdin_graph=(best_n, best_e),
                         timeout=0.93 * float(time_limit))
        n, e = lib.parse_graph_text(text)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
    except Exception:
        pass
    return best_n, list(best_e)
