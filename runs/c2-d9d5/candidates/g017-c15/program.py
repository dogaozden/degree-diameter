"""Two-orbit affine lifts for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs (one A-orbit and one
B-orbit, 2N vertices). This version searches voltage lifts of a 2+2 base graph over
the affine groups F_q x| H (and the elementary abelian groups F_q). The base graph
is K_{2,2} with multiplicities [[m, d-m], [d-m, m]], so every base vertex has degree d.
Each dart carries a group voltage, and the lift has 4N vertices and is d-regular and
bipartite. Left multiplication by G acts on each fibre regularly, so the diameter is
the maximum eccentricity over the four base vertices, which takes four BFS runs.
The Haar case (one base vertex per side, 2N vertices) is kept as a special case of the
same engine, so the search still covers the parent's family.

The C engine binary-searches over candidate (group, base, multiplicity) configurations
sorted by vertex count, with simulated annealing on the voltages at each probe. Python
keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} fallbacks, and every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit voltage lift search over affine groups.
 * Usage: prog d D seed time_limit vmin vmax     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 512
#define MAXC 512
#define MAXN 8192
#define MAXD 32
#define MAXT (2 * MAXD)
#define MAXV (4 * MAXN)
#define MAXCAND 40000
#define ITERS 6000

typedef struct { int q, p, ex, c, N, kb, mm; } Cand;

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

static int factor_pp(int q, int *p, int *ex) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *ex = kk;
    return 1;
}

/* Multiply field elements a, b (base-p digit vectors) modulo the monic f with digits m. */
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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0; /* zero divisor: reducible */
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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). c = 1 gives the additive group. */
static void setup_group(int q, int p, int ex, int c) {
    build_field(q, p, ex);
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

/* ------------------------------------------------------------ base configuration */

/* Base graph: KB A-vertices and KB B-vertices. Darts e are base edges with voltages.
 * KB = 1: all d darts join A0 to B0 (Haar graph, 2N vertices).
 * KB = 2: base K_{2,2} with multiplicities [[mm, d-mm], [d-mm, mm]] (4N vertices). */
static int KB, MM, T;
static int ai_[MAXT], bj_[MAXT], gv[MAXT];
static int fw[MAXT][MAXN], bw[MAXT][MAXN];
static int adjA[2][MAXT], nA[2], adjB[2][MAXT], nB[2];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestG[MAXT];

static void set_config(int kb, int mm) {
    KB = kb;
    MM = mm;
    T = kb * d;
    if (kb == 1) {
        for (int e = 0; e < d; e++) { ai_[e] = 0; bj_[e] = 0; }
    } else {
        for (int e = 0; e < d; e++) { ai_[e] = 0; bj_[e] = (e < mm) ? 0 : 1; }
        for (int e = d; e < 2 * d; e++) { ai_[e] = 1; bj_[e] = (e - d < d - mm) ? 0 : 1; }
    }
    nA[0] = nA[1] = nB[0] = nB[1] = 0;
    for (int e = 0; e < T; e++) {
        adjA[ai_[e]][nA[ai_[e]]++] = e;
        adjB[bj_[e]][nB[bj_[e]]++] = e;
    }
}

static inline int cellof(int e) { return ai_[e] * 2 + bj_[e]; }

/* True if a dart f < upto (f != e) in the same cell as e already uses voltage x. */
static int used_by_cell(int e, int x, int upto) {
    int ce = cellof(e);
    for (int f = 0; f < upto; f++)
        if (f != e && cellof(f) == ce && gv[f] == x) return 1;
    return 0;
}

/* Set dart e to voltage x: fw[e][a] = a*x (A fibre to B fibre), bw[e][b] = b*x^-1. */
static void set_dart(int e, int x) {
    gv[e] = x;
    int xi = ginv(x);
    for (int y = 0; y < GN; y++) {
        fw[e][y] = gmul(y, x);
        bw[e][y] = gmul(y, xi);
    }
}

/* ------------------------------------------------------------ BFS and cost */

/* Vertices: A_i fibre = i*N + x, B_j fibre = (KB + j)*N + y. Number reached within D of src. */
static int bfs_reach(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KB * N) {
                int i = v / N, x = v % N;
                for (int t = 0; t < nA[i]; t++) {
                    int e = adjA[i][t];
                    int u = (KB + bj_[e]) * N + fw[e][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int jj = v / N - KB, y = v % N;
                for (int t = 0; t < nB[jj]; t++) {
                    int e = adjB[jj][t];
                    int u = ai_[e] * N + bw[e][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fibre transitivity: the eccentricity of (u, x) depends only on the base vertex u,
 * so one BFS per base vertex decides the diameter. Zero cost means diameter <= D. */
static long cost_eval(void) {
    int V = 2 * KB * GN;
    long c = 0;
    for (int i = 0; i < KB; i++) c += V - bfs_reach(i * GN);
    for (int j = 0; j < KB; j++) c += V - bfs_reach((KB + j) * GN);
    return c;
}

/* Simulated annealing over the voltages. Returns 1 when cost 0 is reached
 * (the current gv holds the solution), 0 on timeout. */
static int search_cand(double until) {
    int N = GN;
    while (now() < until) {
        for (int e = 0; e < T; e++) {
            int x;
            do { x = rndint(N); } while (used_by_cell(e, x, e));
            set_dart(e, x);
        }
        long cost = cost_eval();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tm = Ts * pow(Te / Ts, (double)it / ITERS);
            int e = rndint(T);
            int x;
            do { x = rndint(N); } while (used_by_cell(e, x, T));
            int old = gv[e];
            set_dart(e, x);
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_dart(e, old);
            }
        }
    }
    return 0;
}

static int run_probe(const Cand *cd, double until) {
    setup_group(cd->q, cd->p, cd->ex, cd->c);
    set_config(cd->kb, cd->mm);
    return search_cand(until);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    long vx = 2L * x->kb * x->N, vy = 2L * y->kb * y->N;
    if (vx != vy) return vx < vy ? -1 : 1;
    return x->mm - y->mm;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long vmin = atol(argv[5]), vmax = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int kb = 1; kb <= 2; kb++) {
        int mlo = (kb == 1) ? 0 : 1;
        int mhi = (kb == 1) ? 0 : d / 2;
        for (int mm = mlo; mm <= mhi; mm++)
            for (int q = 3; q < MAXQ; q++) {
                int p, ex;
                if (!factor_pp(q, &p, &ex)) continue;
                for (int c = 1; c <= q - 1; c++) {
                    if ((q - 1) % c) continue;
                    long N = (long)q * c;
                    long V = 2L * kb * N;
                    if (N > MAXN || V < vmin || V > vmax) continue;
                    if (nc < MAXCAND) {
                        Cand cd = {q, p, ex, c, (int)N, kb, mm};
                        cand[nc++] = cd;
                    }
                }
            }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1;
    long bestV = 0;

    /* Phase 1: binary search over the sorted candidates. Each probe gets an equal
     * share of the remaining time over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (run_probe(&cand[mid], now() + slice)) {
            long V = 2L * cand[mid].kb * cand[mid].N;
            if (V > bestV) {
                bestV = V;
                best_idx = mid;
                memcpy(bestG, gv, sizeof(int) * MAXT);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = (best_idx < 0) ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        Cand *cd = &cand[idx];
        long V = 2L * cd->kb * cd->N;
        if (V <= bestV) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (run_probe(cd, now() + slice)) {
            bestV = V;
            best_idx = idx;
            memcpy(bestG, gv, sizeof(int) * MAXT);
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand *cd = &cand[best_idx];
    setup_group(cd->q, cd->p, cd->ex, cd->c);
    set_config(cd->kb, cd->mm);
    for (int e = 0; e < T; e++) set_dart(e, bestG[e]);
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    int N = GN;
    printf("%d %d\n", 2 * KB * N, T * N);
    for (int e = 0; e < T; e++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", ai_[e] * N + x, (KB + bj_[e]) * N + fw[e][x]);
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

    # Two-orbit voltage lifts (and Haar graphs as a special case), searched in C.
    # Vertex counts are kept between Moore/8 and the Moore bound so that the search
    # covers the whole frontier range.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        vmin = max(best[0] + 1, mb // 8)
        vmax = mb
        if budget > 2.0 and vmin <= vmax:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vmin, vmax],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
