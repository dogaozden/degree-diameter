"""Two-class voltage lifts over affine groups for the bipartite degree-diameter problem.

New idea (not in the parent): the parent's Haar lifts have a single vertex class per
side (base = 2 vertices joined by d darts). Here the base is a bipartite graph with
k in {1, 2} vertices per side. For k = 2 the base has counts
M = [[a, d-a], [d-a, a]] with 1 <= a <= d/2, so each base vertex has degree d. Every
dart (i, j, x) with x in G joins L_{i,g} to R_{j,g*x} for all g in G, where
G = F_q x| H is an affine group (H = the subgroup of F_q^* of order c, c >= 1).
Left and right translations are automorphisms, so the diameter check needs one BFS
per base class (2k BFS runs in total), not per vertex. The order is 2kN with N = |G|.
For d = 9, D = 5, a k = 2 lift on about 625 group elements already reaches 2500
vertices, beating the record 2496.

The C engine enumerates every admissible (k, q, c) whose order lies in [lo, hi],
sorted ascending, and skips any order not above the best found so far. For each
candidate it runs restarts of simulated annealing over the dart voltages. Each
restart picks a random a. The cost is the total number of vertices not reached
within D from the 2k base-class sources. The engine prints the largest valid lift.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-class voltage-lift search over affine groups.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the TOTAL vertex count 2*k*N.
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
#define MAXND 64
#define MAXV 16384
#define MAXCAND 20000
#define ITERS 6000

typedef struct { int q, p, fk, c, bk; long N, tot; } Cand;

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

static void build_field(int q, int p, int fk) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= fk; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < fk; i++)
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
        for (int i = 0; i < fk; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, fk, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, fk, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int fk, int c) {
    build_field(q, p, fk);
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

/* ------------------------------------------------------------ two-class base lift */

/* Base: bk vertices per side (bk = 1 or 2). Base darts e: class i (left) to class j
 * (right) with voltage volt[e]. Left (i,g) ~ right (j, g*volt[e]).
 * Vertex ids: left (i,g) = i*N+g, right (j,h) = bk*N + j*N + h. */
static int bk, N, nd, A_par;
static int dsrc[MAXND], dtgt[MAXND], dpair[MAXND];
static int pst[8], pln[8], npairs;
static int ldart[2][MAXD], rdart[2][MAXD];
static int volt[MAXND];
static int fw[MAXND][MAXN], bw[MAXND][MAXN];
static int sv[MAXND], sA = 0;

static void setup_topology(int a) {
    int M[2][2];
    M[0][0] = d; M[0][1] = 0; M[1][0] = 0; M[1][1] = 0;
    if (bk == 2) {
        M[0][0] = a; M[0][1] = d - a; M[1][0] = d - a; M[1][1] = a;
    }
    npairs = 0;
    nd = 0;
    for (int i = 0; i < bk; i++)
        for (int j = 0; j < bk; j++) {
            int cnt = M[i][j];
            if (cnt <= 0) continue;
            pst[npairs] = nd;
            pln[npairs] = cnt;
            for (int t = 0; t < cnt; t++) {
                dsrc[nd] = i;
                dtgt[nd] = j;
                dpair[nd] = npairs;
                nd++;
            }
            npairs++;
        }
    for (int i = 0; i < bk; i++) {
        int c = 0;
        for (int e = 0; e < nd; e++)
            if (dsrc[e] == i) ldart[i][c++] = e;
    }
    for (int j = 0; j < bk; j++) {
        int c = 0;
        for (int e = 0; e < nd; e++)
            if (dtgt[e] == j) rdart[j][c++] = e;
    }
}

static void set_volt(int e, int x) {
    volt[e] = x;
    int xi = ginv(x);
    for (int g = 0; g < N; g++) {
        fw[e][g] = gmul(g, x);
        bw[e][g] = gmul(g, xi);
    }
}

static int clash_before(int e, int x) {
    int st = pst[dpair[e]];
    for (int t = st; t < e; t++)
        if (volt[t] == x) return 1;
    return 0;
}

static int clash_any(int e, int x) {
    int p = dpair[e], st = pst[p], en = st + pln[p];
    for (int t = st; t < en; t++)
        if (t != e && volt[t] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int stamp_ = 0;
static int vis[MAXV], que[MAXV];

static int bfs_count(int src) {
    int NB = bk * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < NB) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int e = ldart[i][t];
                    int u = NB + dtgt[e] * N + fw[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int r = v - NB;
                int j = r / N, h = r - j * N;
                for (int t = 0; t < d; t++) {
                    int e = rdart[j][t];
                    int u = dsrc[e] * N + bw[e][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Base-class transitivity: one BFS per class (left classes at L_{i,e}, right at R_{j,e}). */
static long cover_cost(void) {
    int NB = bk * N, V = 2 * NB;
    long c = 0;
    for (int i = 0; i < bk; i++) c += (long)(V - bfs_count(i * N));
    for (int j = 0; j < bk; j++) c += (long)(V - bfs_count(NB + j * N));
    return c;
}

static void save_state(void) {
    memcpy(sv, volt, sizeof(int) * (size_t)nd);
    sA = A_par;
}

/* Simulated annealing over voltages. Each restart picks a random block size a for bk=2.
 * Returns 1 when cost 0 is reached (sv/sA hold the solution), 0 on timeout. */
static int search_group(double until) {
    int amax = d / 2;
    while (now() < until) {
        if (bk == 2) A_par = 1 + rndint(amax);
        else A_par = 0;
        setup_topology(A_par);
        for (int e = 0; e < nd; e++) {
            int x;
            do { x = rndint(N); } while (clash_before(e, x));
            set_volt(e, x);
        }
        long cost = cover_cost();
        if (cost == 0) { save_state(); return 1; }
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int e = rndint(nd);
            int x;
            do { x = rndint(N); } while (clash_any(e, x));
            int old = volt[e];
            set_volt(e, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_volt(e, old);
            }
        }
        if (cost == 0) { save_state(); return 1; }
    }
    return 0;
}

static int cmp_tot(const void *a, const void *b) {
    long x = ((const Cand *)a)->tot, y = ((const Cand *)b)->tot;
    return (x > y) - (x < y);
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int bkk = 1; bkk <= 2; bkk++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, fk;
            if (!factor_pp(q, &p, &fk)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long NN = (long)q * c;
                if (NN > MAXN || NN < d) continue;
                long tot = 2L * bkk * NN;
                if (tot < lo || tot > hi) continue;
                if (nc < MAXCAND) {
                    cand[nc].q = q;
                    cand[nc].p = p;
                    cand[nc].fk = fk;
                    cand[nc].c = c;
                    cand[nc].bk = bkk;
                    cand[nc].N = NN;
                    cand[nc].tot = tot;
                    nc++;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_tot);

    long bestTot = 0;
    int bestCi = -1, bestNd = 0, bestA = 0;
    static int bestVolt[MAXND];
    for (int ci = 0; ci < nc; ci++) {
        if (now() > t_end) break;
        if (cand[ci].tot <= bestTot) continue;
        double rem = t_end - now();
        double slice = rem / 8.0;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (slice <= 0) break;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].fk, cand[ci].c);
        N = GN;
        bk = cand[ci].bk;
        if (search_group(now() + slice)) {
            bestTot = cand[ci].tot;
            bestCi = ci;
            bestNd = nd;
            bestA = sA;
            memcpy(bestVolt, sv, sizeof(int) * (size_t)nd);
        }
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand b = cand[bestCi];
    setup_group(b.q, b.p, b.fk, b.c);
    N = GN;
    bk = b.bk;
    setup_topology(bestA);
    for (int e = 0; e < bestNd && e < nd; e++) set_volt(e, bestVolt[e]);
    int NB = bk * N;
    printf("%d %d\n", 2 * NB, nd * N);
    for (int e = 0; e < nd; e++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", dsrc[e] * N + g, NB + dtgt[e] * N + fw[e][g]);
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

    # Two-class voltage lifts over affine groups: search only totals above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 6)
        hi = mb // 2
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
