"""Two-orbit affine and cyclic voltage lifts for the bipartite degree-diameter problem.

New idea in this version: a 4-vertex base lift. Each side of the bipartition is
split into two group orbits, so the graph has 4N vertices for a group of order N.
Left classes L0, L1 and right classes R0, R1 carry voltage blocks with sizes
M = [[a, d-a], [d-a, a]], which makes the graph d-regular. Within a block the
voltages are distinct, so the graph is simple and bipartite by construction.

Left translation preserves all edges and acts transitively on each class, so the
diameter test reduces to four BFS runs, one from each class representative. The
C engine searches over the block sizes a, the voltages, and the groups (cyclic
Z_N and affine F_q x| H). Stage 1 is the single-orbit Haar lift (2N vertices)
over the same group families. Stage 2 is the new 4-orbit lift, with 4N vertices.
Both stages run in the same C engine, and the larger valid result is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search.
 * Usage: prog d D seed time_limit lo hi P
 *   P = 1: Haar-type lift, 2N vertices.  P = 2: 4-orbit lift, 4N vertices.
 *   lo, hi bound the group order N.  Output: "n m" then m lines "u v", or "0 0".
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
#define MAXD 40
#define MAXCAND 20000
#define ITERS 5000

typedef struct { int type, q, p, k, c, N; } Cand;

static int d, D, P;
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

/* ------------------------------------------------------------ groups */
/* GT = 0: cyclic Z_N.  GT = 1: F_q x| H with |H| = GC, element (a, h_j) coded a*GC + j. */

static int GT, GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_group(const Cand *cd) {
    if (cd->type == 0) {
        GT = 0; GQ = 0; GC = 1; GN = cd->N;
        return;
    }
    GT = 1;
    int q = cd->q, p = cd->p, k = cd->k, c = cd->c;
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

static inline int gm(int x, int y) {
    if (GT == 0) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int gi(int x) {
    if (GT == 0) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */
/* Classes: left c = 0..P-1 are vertices c*N+h; right class j is vertex (P+j)*N+h.
 * Block (i,j) has MS[i][j] distinct voltages V[i][j][k]; edge (L_i,g)-(R_j, g*x).
 * Row and column sums of MS are d, so the graph is d-regular and bipartite.
 * Left translation maps each class to itself transitively, so one BFS per class
 * decides the diameter. */

static int MS[2][2];
static int V[2][2][MAXD];
static int NB[4 * MAXN][MAXD];
static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;
static int NV;

static void refresh(void) {
    int N = GN;
    for (int c = 0; c < 2 * P; c++)
        for (int h = 0; h < N; h++) {
            int *nb = NB[c * N + h];
            int idx = 0;
            if (c < P) {
                for (int j = 0; j < P; j++)
                    for (int k = 0; k < MS[c][j]; k++)
                        nb[idx++] = (P + j) * N + gm(h, V[c][j][k]);
            } else {
                int j = c - P;
                for (int i = 0; i < P; i++)
                    for (int k = 0; k < MS[i][j]; k++)
                        nb[idx++] = i * N + gm(h, gi(V[i][j][k]));
            }
        }
}

static int bfs_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *nb = NB[v];
            for (int t = 0; t < d; t++) {
                int u = nb[t];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return tail;
}

static long cost(void) {
    long tot = 0;
    for (int c = 0; c < 2 * P; c++)
        tot += (long)(NV - bfs_count(c * GN));
    return tot;
}

static int in_block(int x, int i, int j, int upto) {
    for (int k = 0; k < upto; k++)
        if (V[i][j][k] == x) return 1;
    return 0;
}

static void random_init(void) {
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int k = 0; k < MS[i][j]; k++) {
                int x;
                do { x = rndint(GN); } while (in_block(x, i, j, k));
                V[i][j][k] = x;
            }
}

/* Simulated annealing over voltages, with random block sizes (P = 2) per restart. */
static int search_group(double until) {
    if (GN <= d) return 0;
    NV = 2 * P * GN;
    while (now() < until) {
        memset(MS, 0, sizeof MS);
        if (P == 1) {
            MS[0][0] = d;
        } else {
            int a = rndint(d + 1);
            MS[0][0] = a;
            MS[1][1] = a;
            MS[0][1] = d - a;
            MS[1][0] = d - a;
        }
        random_init();
        refresh();
        long cst = cost();
        if (cst == 0) return 1;
        double c0 = (double)cst;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cst > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int i = rndint(P), j = rndint(P);
            if (MS[i][j] == 0) continue;
            int k = rndint(MS[i][j]);
            int x;
            do { x = rndint(GN); } while (in_block(x, i, j, MS[i][j]));
            int old = V[i][j][k];
            V[i][j][k] = x;
            refresh();
            long c2 = cost();
            if (c2 <= cst || rnd01() < exp(-(double)(c2 - cst) / T)) {
                cst = c2;
            } else {
                V[i][j][k] = old;
                refresh();
            }
        }
        if (cst == 0) return 1;
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->N > y->N) - (x->N < y->N);
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    P = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (P != 1 && P != 2)) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXN) hi = MAXN;
    if (lo < d + 1) lo = d + 1;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int N = lo; N <= hi && nc < MAXCAND; N++) {
        Cand cd = {0, 0, 0, 0, 1, N};
        cand[nc++] = cd;
    }
    for (int q = 3; q < MAXQ && nc < MAXCAND; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            if (c == 1 && k == 1) continue;   /* same as cyclic Z_q */
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {1, q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Passes over candidates in ascending order. Only candidates whose total
     * vertex count 2*P*N beats the current best are tried. */
    long bestTot = 0;
    int bestCi = -1;
    int bestMS[2][2];
    int bestV[2][2][MAXD];
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            long tot = 2L * P * cand[ci].N;
            if (tot <= bestTot) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice > 6.0) slice = 6.0;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_group(&cand[ci]);
            if (search_group(now() + slice)) {
                bestTot = tot;
                bestCi = ci;
                memcpy(bestMS, MS, sizeof MS);
                memcpy(bestV, V, sizeof V);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&cand[bestCi]);
    NV = 2 * P * GN;
    memcpy(MS, bestMS, sizeof MS);
    memcpy(V, bestV, sizeof V);
    refresh();
    int N = GN;
    int m = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++) m += MS[i][j] * N;
    printf("%d %d\n", 2 * P * N, m);
    for (int i = 0; i < P; i++)
        for (int g = 0; g < N; g++)
            for (int j = 0; j < P; j++)
                for (int k = 0; k < MS[i][j]; k++)
                    printf("%d %d\n", i * N + g, (P + j) * N + gm(g, V[i][j][k]));
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
        deadline = t0 + 0.82 * time_limit - 2.0

        def run_stage(P, lo, hi, secs):
            if secs <= 2.0 or lo > hi:
                return
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(secs, 2), lo, hi, P],
                                 stdin_graph=None, timeout=secs + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph found so far

        # Stage 1 (new): 4-orbit lift, 4N vertices for group order N.
        left = deadline - time.monotonic()
        run_stage(2, max(best[0] // 4 + 1, 2), mb // 4, 0.6 * left)
        # Stage 2: single-orbit (Haar) lift, 2N vertices, with the bound raised by stage 1.
        left = deadline - time.monotonic()
        run_stage(1, max(best[0] // 2 + 1, mb // 8), mb // 3, left - 0.5)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
