"""Two-family affine-group lift search for the bipartite degree-diameter problem.

Family H (Haar): 2 base vertices, d darts, order 2N. Same as the parent: L_g ~ R_{g s}.
Family B (bi-lift): 4 base vertices L0, L1, R0, R1, order 4N. Each left base vertex
has d darts. The dart-count matrix is [[x, d-x], [d-x, x]] for x in 0..d/2. Dart
(a, b, g) joins L^a_z to R^b_{z g}. Left multiplication by G is an automorphism that
is transitive on each of the four fibres, so the diameter check needs four BFS runs,
one from each fibre representative.

Scheduling: one C run. The bi-lift phase gets about half the search budget (ascending
orders, each attempt 25% of the remaining phase time). The Haar phase then gets the
rest. The best valid graph of either family is printed. Python keeps the parent's
valid fallbacks and validates every result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two families over G = F_q x| H (H = subgroup of F_q^* of order c).
 *  Family 0 (Haar): 2 base vertices, d darts, order 2N.
 *  Family 1 (bi-lift): base L0, L1, R0, R1; darts out of each L^a are d in number;
 *      dart counts [[x, d-x],[d-x, x]]; order 4N.
 * Usage: prog d D seed time_limit lo_h hi_h lo_b hi_b     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
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
#define MAXN 8192
#define MAXD 32
#define MAXCAND 8192
#define MAXX 17

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

/* ============================================================ family 0: Haar */

static int S[MAXD], Sinv[MAXD];
static int bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
    }
}

static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static int search_haar(double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        int timed_out = 0;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) { timed_out = 1; break; }
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
        if (timed_out) break;
    }
    return 0;
}

/* ============================================================ family 1: bi-lift */

static int volt[2 * MAXD], vinv[2 * MAXD], eB[2 * MAXD];
static int LB[2][MAXD];
static int fwdE[2 * MAXD][MAXN], bwdE[2 * MAXD][MAXN];
static int bvis[4 * MAXN], bque[4 * MAXN];
static int bstamp = 0;
static int sol_x = 0;
static int sol_v[2 * MAXD];
static int bestBV[2 * MAXD];
static int bestX = 0;

/* Darts 0..d-1 start at L^0, darts d..2d-1 start at L^1.
 * Dart e is assigned to right base vertex eB[e] for the matrix [[x, d-x],[d-x, x]]. */
static void set_config(int x) {
    for (int e = 0; e < 2 * d; e++) {
        int a = e / d, idx = e % d;
        if (a == 0) eB[e] = (idx < x) ? 0 : 1;
        else eB[e] = (idx < d - x) ? 0 : 1;
    }
    int cnt[2] = {0, 0};
    for (int e = 0; e < 2 * d; e++) {
        int b = eB[e];
        LB[b][cnt[b]++] = e;
    }
}

static inline int pid(int e) { return (e / d) * 2 + eB[e]; }

/* Voltages of darts in the same (a, b) pair must be distinct (simple graph). */
static int pair_free(int e, int v) {
    int pe = pid(e);
    for (int f = 0; f < 2 * d; f++)
        if (f != e && volt[f] == v && pid(f) == pe) return 0;
    return 1;
}

static void set_dart(int e, int v) {
    volt[e] = v;
    vinv[e] = ginv(v);
    for (int g = 0; g < GN; g++) {
        fwdE[e][g] = gmul(g, v);
        bwdE[e][g] = gmul(g, vinv[e]);
    }
}

/* Vertices: L^a_x = a*N + x, R^b_y = 2N + b*N + y. */
static int bfs_bi(int src) {
    int N = GN;
    bstamp++;
    int head = 0, tail = 0;
    bque[tail++] = src;
    bvis[src] = bstamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = bque[head++];
            if (v < 2 * N) {
                int a = v / N, x = v % N;
                for (int i = 0; i < d; i++) {
                    int e = a * d + i;
                    int u = 2 * N + eB[e] * N + fwdE[e][x];
                    if (bvis[u] != bstamp) { bvis[u] = bstamp; bque[tail++] = u; }
                }
            } else {
                int w = v - 2 * N;
                int b = w / N, y = w % N;
                for (int i = 0; i < d; i++) {
                    int e = LB[b][i];
                    int u = (e / d) * N + bwdE[e][y];
                    if (bvis[u] != bstamp) { bvis[u] = bstamp; bque[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication acts transitively on each of the 4 fibres, so BFS from the
 * four fibre representatives decides the diameter. */
static long cost_bi(void) {
    int N = GN, V = 4 * N;
    int srcs[4] = {0, N, 2 * N, 3 * N};
    long c = 0;
    for (int s = 0; s < 4; s++) c += (long)(V - bfs_bi(srcs[s]));
    return c;
}

static int search_bi(double until) {
    int N = GN;
    const int iters = 8000;
    int nx = d / 2 + 1;
    int have[MAXX];
    long bestc[MAXX];
    int incv[MAXX][2 * MAXD];
    for (int x = 0; x < MAXX; x++) { have[x] = 0; bestc[x] = 0; }
    int r = 0;
    while (now() < until) {
        int x = r % nx;
        r++;
        set_config(x);
        if (!have[x]) {
            for (int e = 0; e < 2 * d; e++) volt[e] = -1;
            for (int e = 0; e < 2 * d; e++) {
                int v;
                do { v = rndint(N); } while (!pair_free(e, v));
                set_dart(e, v);
            }
        } else {
            for (int e = 0; e < 2 * d; e++) set_dart(e, incv[x][e]);
            for (int t = 0; t < 2; t++) {
                int e = rndint(2 * d), v;
                do { v = rndint(N); } while (!pair_free(e, v));
                set_dart(e, v);
            }
        }
        long cost = cost_bi();
        if (cost == 0) {
            sol_x = x;
            memcpy(sol_v, volt, sizeof(int) * (size_t)(2 * d));
            return 1;
        }
        double c0 = (double)cost;
        double Ts = (have[x] ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        int timed_out = 0;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) { timed_out = 1; break; }
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(2 * d), v;
            do { v = rndint(N); } while (!pair_free(e, v));
            int old = volt[e];
            set_dart(e, v);
            long c2 = cost_bi();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(e, old);
            }
        }
        if (cost == 0) {
            sol_x = x;
            memcpy(sol_v, volt, sizeof(int) * (size_t)(2 * d));
            return 1;
        }
        if (!have[x] || cost < bestc[x]) {
            have[x] = 1;
            bestc[x] = cost;
            memcpy(incv[x], volt, sizeof(int) * (size_t)(2 * d));
        }
        if (timed_out) break;
    }
    return 0;
}

/* ============================================================ scheduling */

static long bestV = 0;
static int bestFam = -1;
static Cand bestC;
static Cand candH[MAXCAND], candB[MAXCAND];

static int enum_cands(int lo, int hi, Cand *out) {
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

static void run_phase(Cand *cs, int n, int fam, double phase_end) {
    for (int ci = 0; ci < n; ci++) {
        double rem = phase_end - now();
        if (rem < 0.3) break;
        long V = (fam ? 4L : 2L) * cs[ci].N;
        if (V <= bestV) continue;
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cs[ci].q, cs[ci].p, cs[ci].k, cs[ci].c);
        int ok = fam ? search_bi(now() + slice) : search_haar(now() + slice);
        if (ok) {
            bestV = V;
            bestFam = fam;
            bestC = cs[ci];
            if (fam) {
                bestX = sol_x;
                memcpy(bestBV, sol_v, sizeof(int) * (size_t)(2 * d));
            } else {
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
    }
}

static void print_haar(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

static void print_bi(void) {
    int N = GN;
    printf("%d %d\n", 4 * N, 2 * N * d);
    for (int a = 0; a < 2; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int e = a * d + i;
                printf("%d %d\n", a * N + x, 2 * N + eB[e] * N + fwdE[e][x]);
            }
}

/* ============================================================ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo_h = atoi(argv[5]), hi_h = atoi(argv[6]);
    int lo_b = atoi(argv[7]), hi_b = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi_h > MAXN) hi_h = MAXN;
    if (hi_b > MAXN) hi_b = MAXN;
    if (lo_h < 2 * d) lo_h = 2 * d;
    if (lo_b < 2 * d) lo_b = 2 * d;

    int nB = enum_cands(lo_b, hi_b, candB);
    int nH = enum_cands(lo_h, hi_h, candH);

    /* Bi-lift phase first (about half the remaining time), then the Haar phase. */
    double bi_end = now() + 0.5 * (t_end - now());
    run_phase(candB, nB, 1, bi_end);
    run_phase(candH, nH, 0, t_end);

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestC.q, bestC.p, bestC.k, bestC.c);
    if (bestFam == 0) {
        for (int i = 0; i < d; i++) set_s(i, bestS[i]);
        print_haar();
    } else {
        set_config(bestX);
        for (int e = 0; e < 2 * d; e++) set_dart(e, bestBV[e]);
        print_bi();
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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        # Haar family: order 2N, group order N in [lo_h, hi_h].
        lo_h = max(best[0] // 2 + 1, mb // 8)
        hi_h = mb // 3
        # Bi-lift family: order 4N, group order N in [lo_b, hi_b].
        lo_b = max(2 * d, best[0] // 4 + 1, mb // 15)
        hi_b = min(1200, mb // 4)
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo_h, hi_h, lo_b, hi_b],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
