"""Two-orbit semidirect Haar lifts for the bipartite degree-diameter problem.

New idea in this version: the parent searches lifts with one left and one right base
vertex (Haar graphs over a group G). This version uses a base with two left orbits
L0, L1 and two right orbits R0, R1. Each left orbit has d darts. The block matrix
    [[x, d-x], [d-x, x]]    (1 <= x <= d/2)
gives the number of darts between each (left, right) orbit pair. A dart with label s
joins L_{i,g} to R_{j,g*s}. The lift has 4|G| vertices, is d-regular and bipartite,
and is simple because labels inside one block are distinct.

Left translations are automorphisms, so the diameter test reduces to four BFS runs, one
from each orbit representative at the identity. The C engine runs simulated annealing
on the labels of each (group, x) candidate. It accepts a graph only after a full
all-pairs BFS check. Groups are semidirect products Z_m x|_r Z_k, which include the
cyclic groups and the affine groups F_p x| H.

Scheduling: candidate groups are tried in ascending order. A candidate is skipped unless
its vertex count beats the fallback. The two-orbit search gets 60% of the time, and the
one-orbit search (the parent's family) gets the rest.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit semidirect Haar lift search.
 * Usage: prog d D seed time_limit lo2 hi2 lo1 hi1 minV     (stdin ignored)
 *   Phase A=2: group orders N in [lo2,hi2], graph order 4N.
 *   Phase A=1: group orders N in [lo1,hi1], graph order 2N.
 * Prints the best valid graph with more than minV vertices, else "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1536
#define MAXD 32
#define MAXT (2 * MAXD)
#define MAXV (4 * MAXN)
#define MAXCAND 300000
#define MAXTRIP 400000

typedef struct { int N, m, k, r; } Grp;
typedef struct { int N, g, x; unsigned rk; } Trip;

static int d, D, minV;
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
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k
 * Element (a,b) is coded a*k+b. Product: (a,b)(c,e) = (a + r^b c, b+e). */
static int GN, GM, GK, GR;
static int PWR[MAXN];
static int MT[MAXN][MAXN];
static int INV[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    PWR[0] = 1 % m;
    for (int b = 1; b < k; b++) PWR[b] = (PWR[b - 1] * r) % m;
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            int na = (a + PWR[b] * c) % m;
            int nb = (b + e) % k;
            MT[x][y] = na * k + nb;
        }
    }
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int na = (m - (PWR[nb] * a) % m) % m;
        INV[x] = na * k + nb;
    }
}

static Grp grp[MAXCAND];
static int ngrp = 0;
static Trip trips[MAXTRIP];

static void add_grp(int N, int m, int k, int r) {
    if (ngrp < MAXCAND) {
        grp[ngrp].N = N; grp[ngrp].m = m; grp[ngrp].k = k; grp[ngrp].r = r;
        ngrp++;
    }
}

/* All groups Z_m x|_r Z_k with m*k = N for N in [lo, hi]; r^k = 1 mod m, gcd(r,m)=1. */
static void gen_groups(int lo, int hi) {
    ngrp = 0;
    for (int N = lo; N <= hi; N++) {
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) { add_grp(N, 1, k, 0); continue; }
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                int p = 1;
                for (int t = 0; t < k; t++) p = (p * r) % m;
                if (p == 1) add_grp(N, m, k, r);
            }
        }
    }
}

/* ------------------------------------------------------------ lift state
 * Left orbits i in 0..A-1 (vertices i*GN+g), right orbits j (vertices AN+j*GN+h).
 * Dart e joins L_{SRC[e],g} to R_{DST[e],g*LAB[e]}. Each left and right orbit has d darts. */
static int A, T, AN;
static int SRC[MAXT], DST[MAXT], BLK[MAXT], LAB[MAXT], ILAB[MAXT];
static int LEFT[2][MAXD], RIGHT[2][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestV, bestA, bestGM, bestGK, bestGR, bestT;
static int bSRC[MAXT], bDST[MAXT], bLAB[MAXT];

static int setup_config(int a_, int x) {
    A = a_;
    T = 0;
    if (A == 1) {
        for (int t = 0; t < d; t++) { SRC[T] = 0; DST[T] = 0; T++; }
    } else {
        int blk[2][2] = {{x, d - x}, {d - x, x}};
        for (int i = 0; i < 2; i++)
            for (int j = 0; j < 2; j++)
                for (int t = 0; t < blk[i][j]; t++) {
                    SRC[T] = i; DST[T] = j; T++;
                }
    }
    int lc[2] = {0, 0}, rc[2] = {0, 0};
    for (int e = 0; e < T; e++) {
        BLK[e] = SRC[e] * A + DST[e];
        if (lc[SRC[e]] >= d || rc[DST[e]] >= d) return 0;
        LEFT[SRC[e]][lc[SRC[e]]++] = e;
        RIGHT[DST[e]][rc[DST[e]]++] = e;
    }
    for (int i = 0; i < A; i++)
        if (lc[i] != d || rc[i] != d) return 0;
    return 1;
}

static void set_label(int e, int s) {
    LAB[e] = s;
    ILAB[e] = INV[s];
}

/* True if some other dart in the same block already uses label s. */
static int block_conflict(int e, int s) {
    for (int f = 0; f < T; f++)
        if (f != e && BLK[f] == BLK[e] && LAB[f] == s) return 1;
    return 0;
}

static void init_labels(void) {
    for (int e = 0; e < T; e++) LAB[e] = -1;
    for (int e = 0; e < T; e++) {
        int s;
        do { s = rndint(GN); } while (block_conflict(e, s));
        set_label(e, s);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < AN) {
                int i = v / GN, g = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int e = LEFT[i][t];
                    int u = AN + DST[e] * GN + MT[g][LAB[e]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - AN;
                int j = w / GN, h = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int e = RIGHT[j][t];
                    int u = SRC[e] * GN + MT[h][ILAB[e]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit representatives suffice: left translations are automorphisms. */
static long cost_eval(void) {
    long c = 0;
    int V = 2 * AN;
    for (int i = 0; i < A; i++) c += V - bfs_reach(i * GN);
    for (int j = 0; j < A; j++) c += V - bfs_reach(AN + j * GN);
    return c;
}

static int verify_full(void) {
    int V = 2 * AN;
    for (int v = 0; v < V; v++)
        if (bfs_reach(v) != V) return 0;
    return 1;
}

static void try_record(void) {
    int V = 2 * A * GN;
    if (V <= bestV) return;
    if (!verify_full()) return;
    bestV = V;
    bestA = A; bestGM = GM; bestGK = GK; bestGR = GR; bestT = T;
    for (int e = 0; e < T; e++) {
        bSRC[e] = SRC[e];
        bDST[e] = DST[e];
        bLAB[e] = LAB[e];
    }
}

/* Simulated annealing over the labels of the fixed block structure.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
static int search(double until) {
    const int iters = 20000;
    AN = A * GN;
    while (now() < until) {
        init_labels();
        long cost = cost_eval();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 2.0, Te = 0.2;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tcur = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(T);
            int s;
            do { s = rndint(GN); } while (block_conflict(e, s));
            int old = LAB[e];
            set_label(e, s);
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tcur)) {
                cost = c2;
            } else {
                set_label(e, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int cmp_trip(const void *a, const void *b) {
    const Trip *x = a, *y = b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->rk != y->rk) return x->rk < y->rk ? -1 : 1;
    if (x->x != y->x) return x->x < y->x ? -1 : 1;
    return 0;
}

/* Try (group, x) candidates in ascending order of N, skipping any not beating bestV. */
static void run_phase(int A_, double until, int lo, int hi, int xmax) {
    gen_groups(lo, hi);
    int nt = 0;
    for (int g = 0; g < ngrp; g++) {
        unsigned rk = (unsigned)rnd();
        int xs = (A_ == 1) ? 1 : xmax;
        for (int x = 1; x <= xs && nt < MAXTRIP; x++) {
            trips[nt].N = grp[g].N;
            trips[nt].g = g;
            trips[nt].x = x;
            trips[nt].rk = rk;
            nt++;
        }
    }
    qsort(trips, (size_t)nt, sizeof(Trip), cmp_trip);
    int lastg = -1;
    for (int t = 0; t < nt; t++) {
        Trip tr = trips[t];
        if (2 * A_ * tr.N <= bestV) continue;
        double rem = until - now();
        if (rem < 0.3) break;
        double slice = 0.1 * rem;
        if (slice < 0.4) slice = 0.4;
        if (slice > 5.0) slice = 5.0;
        if (slice > rem) slice = rem;
        if (tr.g != lastg) {
            setup_group(grp[tr.g].m, grp[tr.g].k, grp[tr.g].r);
            lastg = tr.g;
        }
        if (!setup_config(A_, tr.x)) continue;
        AN = A_ * GN;
        if (search(now() + slice)) try_record();
    }
}

static void print_best(void) {
    if (bestV <= minV) { printf("0 0\n"); return; }
    setup_group(bestGM, bestGK, bestGR);
    int n = 2 * bestA * GN;
    printf("%d %d\n", n, bestT * GN);
    int off = bestA * GN;
    for (int e = 0; e < bestT; e++)
        for (int g = 0; g < GN; g++)
            printf("%d %d\n", bSRC[e] * GN + g, off + bDST[e] * GN + MT[g][bLAB[e]]);
}

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo2 = atoi(argv[5]), hi2 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    minV = atoi(argv[9]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    bestV = minV;
    bestT = 0;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (hi2 > MAXN) hi2 = MAXN;
    if (hi1 > MAXN) hi1 = MAXN;

    double t_split = now() + 0.6 * (t_end - now());
    if (lo2 <= hi2 && d >= 2)
        run_phase(2, t_split, lo2, hi2, d / 2);
    if (lo1 <= hi1)
        run_phase(1, t_end, lo1, hi1, 1);

    print_best();
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

    # Search: two-orbit (base size 2) semidirect Haar lifts first, then the one-orbit family.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        minV = best[0]
        lo2 = max(mb // 16, 2 * d)
        hi2 = min(max(lo2 + 1, mb // 10), 800)
        lo1 = max(minV // 2 + 1, mb // 8, 2 * d)
        hi1 = min(max(lo1, mb // 4), 1400)
        if budget > 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo2, hi2, lo1, hi1, minV],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
