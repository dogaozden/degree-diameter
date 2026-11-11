"""Multi-orbit affine-group bi-Cayley lifts for the bipartite degree-diameter problem.

New construction in this version: the parent searches one-orbit Haar graphs
(2N vertices). Here the search also uses two left orbits and two right orbits over
the same affine group G = F_q x| H (order N = q*c), giving 4N vertices.

Vertices: left (i, g) and right (j, h) for i, j in {0, 1}, g, h in G.
Edges: (i, g) ~ (j, g*s) for s in S_ij, where the block sizes are
    |S_00| = |S_11| = a,   |S_01| = |S_10| = d - a,
so every vertex has degree d (row and column sums are d). Each block is a set of
distinct group elements, which makes the graph simple. Left multiplication by G
preserves every block, so each of the four orbits is vertex-transitive. Diameter
<= D therefore reduces to four BFS runs, from (0,e), (1,e), (0,e) and (1,e) on the
right side.

The C engine anneals the four block sets with iterated restarts from the incumbent.
It first runs the four-orbit search on about 70% of the time budget. Then it runs
the parent's one-orbit Haar search on the rest, and keeps whichever graph is larger.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine-group bi-Cayley lift search.
 * Usage: prog d D seed time_limit lo4 hi4 lo1 hi1     (stdin ignored)
 * Phase 1 (about 70% of time): NO = 2 orbits per side, order 4N, shape
 *   [[a, d-a], [d-a, a]] with a in {d/2, ..., 1}.
 * Phase 2 (rest): NO = 1 (Haar, order 2N), only if it beats phase 1.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 4096
#define MAXD 32
#define MAXCAND 8192
#define MAXV (4 * MAXN)

typedef struct { int q, p, k, c, N; } Cand;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[40];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ bi-Cayley state */

static int NO;                       /* orbits per side: 1 (Haar) or 2 */
static int cnt[2][2];                /* block sizes */
static int E[2][2][MAXD];            /* connection elements per block */
/* Left (i,g) = i*N+g; right (j,h) = NO*N + j*N + h.
 * FL[i][j][k][g] = right neighbour of left (i,g) via element E[i][j][k].
 * FR[i][j][k][h] = left neighbour of right (j,h) via element E[i][j][k]. */
static int FL[2][2][MAXD][MAXN];
static int FR[2][2][MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_shape(int a) {
    if (NO == 1) {
        cnt[0][0] = d;
        cnt[0][1] = cnt[1][0] = cnt[1][1] = 0;
    } else {
        cnt[0][0] = cnt[1][1] = a;
        cnt[0][1] = cnt[1][0] = d - a;
    }
}

static void set_el(int i, int j, int k, int x) {
    E[i][j][k] = x;
    int xi = ginv(x);
    int off = NO * GN;
    for (int g = 0; g < GN; g++) {
        FL[i][j][k][g] = off + j * GN + gmul(g, x);
        FR[i][j][k][g] = i * GN + gmul(g, xi);
    }
}

static int in_block(int i, int j, int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (E[i][j][t] == x) return 1;
    return 0;
}

static int pick_new(int i, int j, int upto) {
    int x;
    do { x = rndint(GN); } while (in_block(i, j, x, upto));
    return x;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int MN = NO * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < MN) {
                int i = v / GN, g = v - i * GN;
                for (int j = 0; j < NO; j++)
                    for (int k = 0; k < cnt[i][j]; k++) {
                        int u = FL[i][j][k][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            } else {
                int r = v - MN;
                int j = r / GN, h = r - j * GN;
                for (int i = 0; i < NO; i++)
                    for (int k = 0; k < cnt[i][j]; k++) {
                        int u = FR[i][j][k][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            }
        }
    }
    return tail;
}

/* Sources: one representative per orbit (identity element, index 0). */
static long cover_cost(void) {
    long V = 2L * NO * GN, c = 0;
    for (int o = 0; o < 2 * NO; o++)
        c += V - bfs_count(o * GN);
    return c;
}

/* Iterated annealing over the block sets of the current group and shape.
 * Round 1 starts from random sets; later rounds perturb the incumbent (two
 * elements replaced) and anneal from a lower starting temperature.
 * Returns 1 when cost 0 is reached (E holds the valid sets), 0 on timeout. */
static int search_group(double until, int a) {
    set_shape(a);
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incE[2][2][MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < NO; i++)
                for (int j = 0; j < NO; j++)
                    for (int k = 0; k < cnt[i][j]; k++)
                        set_el(i, j, k, pick_new(i, j, k));
        } else {
            for (int i = 0; i < NO; i++)
                for (int j = 0; j < NO; j++)
                    for (int k = 0; k < cnt[i][j]; k++)
                        set_el(i, j, k, incE[i][j][k]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(NO), j = rndint(NO);
                int k = rndint(cnt[i][j]);
                set_el(i, j, k, pick_new(i, j, cnt[i][j]));
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(NO), j = rndint(NO);
            int k = rndint(cnt[i][j]);
            int old = E[i][j][k];
            set_el(i, j, k, pick_new(i, j, cnt[i][j]));
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_el(i, j, k, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incE, E, sizeof(E));
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    int V = 2 * NO * N;
    long m = (long)NO * N * d;
    printf("%d %ld\n", V, m);
    for (int i = 0; i < NO; i++)
        for (int g = 0; g < N; g++) {
            int v = i * N + g;
            for (int j = 0; j < NO; j++)
                for (int k = 0; k < cnt[i][j]; k++)
                    printf("%d %d\n", v, FL[i][j][k][g]);
        }
}

/* ------------------------------------------------------------ candidates & best */

static int bestNO = 0, bestQ, bestP, bestK, bestC, bestN, bestA;
static int bestTotal = 0;
static int bestE[2][2][MAXD];

static void record(int no, Cand cd, int a) {
    bestNO = no;
    bestQ = cd.q;
    bestP = cd.p;
    bestK = cd.k;
    bestC = cd.c;
    bestN = cd.N;
    bestA = a;
    bestTotal = 2 * no * cd.N;
    memcpy(bestE, E, sizeof(E));
}

/* All (q, c) with N = q*c in [lo, hi], sorted ascending by N. */
static int make_cands(Cand *out, int lo, int hi) {
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi || N > MAXN) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                out[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = out[i];
        int j = i - 1;
        while (j >= 0 && out[j].N > t.N) { out[j + 1] = out[j]; j--; }
        out[j + 1] = t;
    }
    return nc;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo4 = atoi(argv[5]), hi4 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi4 > MAXN) hi4 = MAXN;
    if (hi1 > MAXN) hi1 = MAXN;
    if (lo4 < 2 * d) lo4 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;

    int aList[MAXD], na = 0;
    for (int a = d / 2; a >= 1; a--) aList[na++] = a;

    static Cand c4[MAXCAND], c1[MAXCAND];
    int n4 = make_cands(c4, lo4, hi4);
    int n1 = make_cands(c1, lo1, hi1);

    /* Phase 1: four-orbit lifts (order 4N), ascending N, all shapes a per N. */
    double p1_end = t0 + 0.7 * (t_end - t0);
    int stop = 0;
    for (int ci = 0; ci < n4 && !stop; ci++) {
        Cand cd = c4[ci];
        if (4L * cd.N <= bestTotal) continue;
        int found = 0;
        for (int ai = 0; ai < na && !found && !stop; ai++) {
            double rem = p1_end - now();
            if (rem < 0.3) { stop = 1; break; }
            double slice = 0.12 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(cd.q, cd.p, cd.k, cd.c);
            NO = 2;
            if (search_group(now() + slice, aList[ai])) {
                found = 1;
                record(2, cd, aList[ai]);
            }
        }
    }

    /* Phase 2: one-orbit Haar lifts (order 2N), only where they beat phase 1. */
    for (int ci = 0; ci < n1; ci++) {
        Cand cd = c1[ci];
        if (2L * cd.N <= bestTotal) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cd.q, cd.p, cd.k, cd.c);
        NO = 1;
        if (search_group(now() + slice, d)) record(1, cd, d);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestQ, bestP, bestK, bestC);
    NO = bestNO;
    set_shape(bestA);
    memcpy(E, bestE, sizeof(E));
    for (int i = 0; i < NO; i++)
        for (int j = 0; j < NO; j++)
            for (int k = 0; k < cnt[i][j]; k++)
                set_el(i, j, k, E[i][j][k]);
    print_result();
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
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # Search: multi-orbit affine-group lifts (phase 1) then Haar lifts (phase 2).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo4 = max(best[0] // 4 + 1, mb // 16)   # group orders N; total 4N
        hi4 = mb // 4
        lo1 = max(best[0] // 2 + 1, mb // 8)    # group orders N; total 2N
        hi1 = mb // 3
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo4, hi4, lo1, hi1],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
