"""Two-orbit bi-Cayley lifts over affine groups for the bipartite degree-diameter problem.

Construction change: the parent searched only Haar graphs (one orbit per side) over
affine groups F_q x| H. This version also searches a two-orbit family. Left vertices
L_{i,g} and right vertices R_{j,h} (i, j in {0,1}, g, h in G) are joined by
L_{i,g} ~ R_{j, g*s} for s in S_{ij}. Block sizes are |S00| = |S11| = x and
|S01| = |S10| = d - x, so every vertex has degree d. The graph has 4|G| vertices.
Left and right translations act regularly on each orbit class, so diameter <= D
reduces to four BFS runs, from L_{0,e}, L_{1,e}, R_{0,e} and R_{1,e}.

The one-orbit Haar family is kept as a first phase, since it already reproduces the
parent's result. The two-orbit phase then searches for orders above that.
Every returned graph is checked with lib.is_valid, and the K_{d,d} / projective-plane /
Araujo-Lopez / W(q) baselines remain as fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over affine groups F_q x| H.
 * Usage: prog d D seed time_limit lo1 hi1 lo2 hi2   (stdin ignored)
 * Phase 1: K=1 (Haar graph, 2N vertices) with orders in [lo1, hi1].
 * Phase 2: K=2 (two orbits per side, 4N vertices) with orders in [lo2, hi2].
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
#define MAXN 2400
#define MAXD 32
#define MAXK 2
#define MAXTOT (MAXK * MAXD)
#define MAXCAND 8192

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
    int pa[16], pb[16], prod[32];
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
static int MT[MAXN * MAXN];   /* MT[x*GN+y] = x*y in G */
static int INV[MAXN];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is 0. */
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

static void build_tables(void) {
    int N = GN;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul(x, y);
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* ------------------------------------------------------------ bi-Cayley structure */

/* K orbits per side (K = 1 or 2). Entry e is a connection element s with block
 * (row, col): L_{row,g} ~ R_{col, g*s}. Each row and each column has exactly d entries. */
static int KK;
static int TOT;
static int ENT_ROW[MAXTOT], ENT_COL[MAXTOT], ENT_BLK[MAXTOT], VAL[MAXTOT];
static int rowEnt[MAXK][MAXD], colEnt[MAXK][MAXD];

static void setup_blocks(int K, int x) {
    int a[MAXK][MAXK];
    memset(a, 0, sizeof(a));
    KK = K;
    if (K == 1) a[0][0] = d;
    else { a[0][0] = x; a[0][1] = d - x; a[1][0] = d - x; a[1][1] = x; }
    TOT = 0;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            for (int t = 0; t < a[i][j]; t++) {
                ENT_ROW[TOT] = i;
                ENT_COL[TOT] = j;
                ENT_BLK[TOT] = i * K + j;
                VAL[TOT] = -1;
                TOT++;
            }
    for (int i = 0; i < K; i++) {
        int c = 0;
        for (int e = 0; e < TOT; e++) if (ENT_ROW[e] == i) rowEnt[i][c++] = e;
    }
    for (int j = 0; j < K; j++) {
        int c = 0;
        for (int e = 0; e < TOT; e++) if (ENT_COL[e] == j) colEnt[j][c++] = e;
    }
}

/* Entries within the same block must have distinct values. */
static int free_for(int e, int v) {
    for (int f = 0; f < TOT; f++)
        if (f != e && ENT_BLK[f] == ENT_BLK[e] && VAL[f] == v) return 0;
    return 1;
}

/* ------------------------------------------------------------ BFS and cost */

static int VIS[4 * MAXN], QUE[4 * MAXN];
static int stamp_ = 0;

/* Vertices: L_{i,g} = i*GN + g, R_{j,h} = KK*GN + j*GN + h.
 * Returns the number of vertices within distance D of src. */
static int bfs_count(int src) {
    int NL = KK * GN;
    stamp_++;
    int head = 0, tail = 0;
    QUE[tail++] = src;
    VIS[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = QUE[head++];
            if (v < NL) {
                int i = v / GN, g = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int e = rowEnt[i][t];
                    int u = NL + ENT_COL[e] * GN + MT[g * GN + VAL[e]];
                    if (VIS[u] != stamp_) { VIS[u] = stamp_; QUE[tail++] = u; }
                }
            } else {
                int w = v - NL;
                int j = w / GN, h = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int e = colEnt[j][t];
                    int u = ENT_ROW[e] * GN + MT[h * GN + INV[VAL[e]]];
                    if (VIS[u] != stamp_) { VIS[u] = stamp_; QUE[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Translations act regularly on each orbit class, so the representatives
 * L_{i,e} and R_{j,e} decide the diameter. Cost = total unreached pairs. */
static long cover_cost(void) {
    long NV = 2L * KK * GN, c = 0;
    for (int i = 0; i < KK; i++) c += NV - bfs_count(i * GN);
    for (int j = 0; j < KK; j++) c += NV - bfs_count(KK * GN + j * GN);
    return c;
}

/* Simulated annealing over the connection elements in the current group.
 * Returns 1 when cost 0 is reached (VAL holds the solution), 0 on timeout. */
static int search_group(int K, double until, int *xout) {
    const int iters = 8000;
    while (now() < until) {
        int x = (K == 2) ? 1 + rndint(d - 1) : d;
        setup_blocks(K, x);
        for (int e = 0; e < TOT; e++) {
            int v;
            do { v = rndint(GN); } while (!free_for(e, v));
            VAL[e] = v;
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(TOT);
            int v;
            do { v = rndint(GN); } while (!free_for(e, v));
            int old = VAL[e];
            VAL[e] = v;
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                VAL[e] = old;
            }
        }
        if (cost == 0) { *xout = x; return 1; }
    }
    return 0;
}

/* ------------------------------------------------------------ best record */

static int bestV = 0, bestK = 0, bestX = 0;
static int bestQ, bestP, bestKp, bestC;
static int bestVal[MAXTOT];

/* Binary search over candidate orders for K orbits per side, using time until `until`. */
static void phase(int K, int lo, int hi, double until) {
    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int a = 0, b = nc - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = until - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        build_tables();
        int x = 0;
        if (search_group(K, now() + slice, &x)) {
            int V = 2 * K * cand[mid].N;
            if (V > bestV) {
                bestV = V;
                bestK = K;
                bestX = x;
                bestQ = cand[mid].q;
                bestP = cand[mid].p;
                bestKp = cand[mid].k;
                bestC = cand[mid].c;
                for (int e = 0; e < TOT; e++) bestVal[e] = VAL[e];
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
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
    int lo1 = atoi(argv[5]), hi1 = atoi(argv[6]);
    int lo2 = atoi(argv[7]), hi2 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi1 > MAXN) hi1 = MAXN;
    if (hi2 > MAXN) hi2 = MAXN;
    if (lo1 < 2) lo1 = 2;
    if (lo2 < 2) lo2 = 2;

    /* Phase 1: one orbit per side (Haar), 40% of the time. */
    double split = t0 + 0.4 * (t_end - t0);
    if (lo1 <= hi1) phase(1, lo1, hi1, split);

    /* Phase 2: two orbits per side, using the remaining time. */
    if (lo2 <= hi2) phase(2, lo2, hi2, t_end);

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestQ, bestP, bestKp, bestC);
    build_tables();
    setup_blocks(bestK, bestX);
    for (int e = 0; e < TOT; e++) VAL[e] = bestVal[e];
    int N = GN, K = bestK;
    printf("%d %d\n", 2 * K * N, K * N * d);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++) {
                int e = rowEnt[i][t];
                printf("%d %d\n", i * N + g, K * N + ENT_COL[e] * N + MT[g * N + VAL[e]]);
            }
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

    # Bi-Cayley lifts over affine groups (one or two orbits per side).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        # K=1 graphs have 2N vertices (N <= mb/2); K=2 graphs have 4N (N <= mb/4).
        lo1 = max(best[0] // 2 + 1, mb // 8, 2 * d)
        hi1 = min(mb // 2, 2400)
        lo2 = max(best[0] // 4 + 1, mb // 16, 2 * d)
        hi2 = min(mb // 4, 2400)
        if budget > 2.0 and (lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo1, hi1, lo2, hi2],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
