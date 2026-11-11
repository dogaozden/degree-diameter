"""Multi-fiber voltage lifts over affine and cyclic groups for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs, which are one-fiber lifts over
an affine group. Here the base is a d-regular bipartite multigraph on b + b vertices (b = 1..3),
written as d perfect matchings (sigma_i) with a group voltage w_{i,j} on each dart. The lift has
2*b*|G| vertices. Left multiplication by G is an automorphism that fixes each fiber, so diameter is
checked with 2b BFS runs, from the identity of each fiber. Group choices are the affine family
F_q x| H (c >= 1) and cyclic Z_m for any m. Search is simulated annealing over the voltages and
the matchings. Duplicate edges created by parallel darts are removed at output, so degree stays <= d.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every returned
graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-fiber voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count n = 2*b*N.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
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
#define MAXB 3
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 16384

typedef struct { int mode, q, p, k, c, b, N, n; } Cand;

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

/* ------------------------------------------------------------ groups */

/* MODE 0: affine group F_q x| H, element (a, h_j) coded as a*GC + j.
 * MODE 1: cyclic group Z_GN. */
static int MODE = 0;
static int GQ = 0, GC = 1, GN = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    MODE = 0;
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

static void setup_cyclic(int m) {
    MODE = 1;
    GQ = 0;
    GC = 1;
    GN = m;
}

static inline int gmul(int x, int y) {
    if (MODE == 1) {
        int r = x + y;
        return r >= GN ? r - GN : r;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    if (MODE == 1) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

/* Vertices: left (j, g) = j*GN + g for j < curb; right (k, h) = curb*GN + k*GN + h.
 * Dart i of left fiber j goes to right fiber SG[i][j] with voltage W[i][j]:
 * (j, g) ~ (SG[i][j], g * W[i][j]). Each SG[i] is a permutation of the fibers. */
static int curb = 1;
static int W[MAXD][MAXB], WI[MAXD][MAXB];
static int SG[MAXD][MAXB], SGI[MAXD][MAXB];
static int bestW[MAXD][MAXB], bestSG[MAXD][MAXB];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_volt(int i, int j, int w) {
    W[i][j] = w;
    WI[i][j] = ginv(w);
}

static void swap_layer(int i, int j1, int j2) {
    int t = SG[i][j1];
    SG[i][j1] = SG[i][j2];
    SG[i][j2] = t;
    SGI[i][SG[i][j1]] = j1;
    SGI[i][SG[i][j2]] = j2;
}

static void init_random(void) {
    for (int i = 0; i < d; i++) {
        int perm[MAXB];
        for (int j = 0; j < curb; j++) {
            perm[j] = j;
            set_volt(i, j, rndint(GN));
        }
        for (int j = curb - 1; j > 0; j--) {
            int r = rndint(j + 1);
            int t = perm[j];
            perm[j] = perm[r];
            perm[r] = t;
        }
        for (int j = 0; j < curb; j++) {
            SG[i][j] = perm[j];
            SGI[i][perm[j]] = j;
        }
    }
}

/* i-th neighbour of vertex v. */
static inline int nbr(int v, int i) {
    int bN = curb * GN;
    if (v < bN) {
        int j = v / GN;
        int g = v - j * GN;
        int k = SG[i][j];
        return bN + k * GN + gmul(g, W[i][j]);
    } else {
        int u = v - bN;
        int k = u / GN;
        int h = u - k * GN;
        int j = SGI[i][k];
        return j * GN + gmul(h, WI[i][j]);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int V = 2 * curb * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        if (tail == V) break;
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int i = 0; i < d; i++) {
                int u = nbr(v, i);
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Left multiplication fixes each fiber, so one BFS per fiber (from its identity) per side suffices. */
static long cover_cost(void) {
    int V = 2 * curb * GN;
    long c = 0;
    for (int j = 0; j < curb; j++) {
        c += (long)(V - bfs_reach(j * GN));
        c += (long)(V - bfs_reach(curb * GN + j * GN));
    }
    return c;
}

/* Annealing over voltages and fiber matchings for the current group and base size. */
static int search_cfg(double until) {
    const int iters = 6000;
    while (now() < until) {
        init_random();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (curb > 1 && rndint(10) < 3) {
                int i = rndint(d), j1 = rndint(curb), j2 = rndint(curb);
                if (j1 == j2) continue;
                swap_layer(i, j1, j2);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else swap_layer(i, j1, j2);
            } else {
                int i = rndint(d), j = rndint(curb);
                int old = W[i][j];
                set_volt(i, j, rndint(GN));
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_volt(i, j, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void setup_cand(const Cand *cd) {
    curb = cd->b;
    if (cd->mode == 0) setup_affine(cd->q, cd->p, cd->k, cd->c);
    else setup_cyclic(cd->N);
}

static void print_result(void) {
    int bN = curb * GN;
    int V = 2 * bN;
    long m = 0;
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < d; i++) {
            int u = nbr(v, i), dup = 0;
            for (int t = 0; t < i; t++)
                if (nbr(v, t) == u) { dup = 1; break; }
            if (!dup) m++;
        }
    printf("%d %ld\n", V, m);
    for (int v = 0; v < bN; v++)
        for (int i = 0; i < d; i++) {
            int u = nbr(v, i), dup = 0;
            for (int t = 0; t < i; t++)
                if (nbr(v, t) == u) { dup = 1; break; }
            if (!dup) printf("%d %d\n", v, u);
        }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->n != b->n) return a->n < b->n ? -1 : 1;
    return 0;
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXV) hi = MAXV;

    int nc = 0;
    for (int b = 1; b <= MAXB; b++) {
        long twob = 2L * b;
        /* Affine groups, q >= 3, c | q-1, c >= 1. */
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                long n = twob * N;
                if (N > MAXN || n < lo || n > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {0, q, p, k, c, b, (int)N, (int)n};
                    cand[nc++] = cd;
                }
            }
        }
        /* Cyclic groups Z_m. */
        long Nlo = (lo + twob - 1) / twob, Nhi = hi / twob;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long m = Nlo; m <= Nhi; m++) {
            if (m < 2) continue;
            if (nc < MAXCAND) {
                Cand cd = {1, 0, 0, 0, 1, b, (int)m, (int)(twob * m)};
                cand[nc++] = cd;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestn = 0;

    /* Phase 1: binary search over total vertex count. Each probe gets an equal
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
        setup_cand(&cand[mid]);
        if (search_cfg(now() + slice)) {
            if (cand[mid].n > bestn) {
                bestn = cand[mid].n;
                best_idx = mid;
                memcpy(bestW, W, sizeof W);
                memcpy(bestSG, SG, sizeof SG);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few sizes above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].n <= bestn) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_cand(&cand[idx]);
        if (search_cfg(now() + slice)) {
            bestn = cand[idx].n;
            best_idx = idx;
            memcpy(bestW, W, sizeof W);
            memcpy(bestSG, SG, sizeof SG);
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
    setup_cand(&cand[best_idx]);
    memcpy(W, bestW, sizeof W);
    memcpy(SG, bestSG, sizeof SG);
    for (int i = 0; i < d; i++)
        for (int j = 0; j < curb; j++) {
            WI[i][j] = ginv(W[i][j]);
            SGI[i][SG[i][j]] = j;
        }
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

    # Multi-fiber voltage lifts over affine and cyclic groups. Only graphs with more
    # vertices than the current best are useful, so the search range starts just above it.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0] + 1
        hi = mb
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
