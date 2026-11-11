"""Non-cyclic group voltage lifts with a 2-vertex base for the bipartite degree-diameter problem.

New construction in this version. Take a finite group G = Z_m x|_r Z_k (order N, r^k = 1 mod m).
The base multigraph has two left and two right vertices (a = 2):
    L0-R0: p darts,  L0-R1: d-p darts,  L1-R0: d-p darts,  L1-R1: p darts.
A dart (u, w, g) joins (u, x) to (w, x*g) for every x in G. Each left and right base vertex
then has degree d, the lift is a simple bipartite d-regular graph on 4N vertices, and the
darts inside one base pair must carry distinct labels. Left translations are automorphisms
that act transitively on each fibre, so diameter <= D is checked by BFS from the four
representatives (u, e). The a = 1 case (one base pair with d darts, 2N vertices) is the
Haar-type member of the same family.

Search: candidates (total order T, group, p, a) are enumerated in increasing T. Each
candidate gets a time slice, and the dart labels are annealed. Rounds after the first
perturb the incumbent labels instead of restarting. The projective-plane and
Araujo-Lopez baselines in Python are the safe fallback, and every result passes lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Non-cyclic lift search over Z_m x|_r Z_k with a 1- or 2-vertex base per side.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count T = 2*a*N.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXDART 64
#define MAXN 4096
#define MAXV (4 * MAXN)
#define MAXCAND 80000

typedef struct { int a, m, k, r, p, T; } Cand;

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k
 * Element (a,b) is coded a*k+b. Product: (a,b)(c,e) = (a + r^b c, b + e). */

static int GM, GK, GN, GR;
static int rpow[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    GR = r;
    rpow[0] = 1 % m;
    for (int b = 1; b < k; b++) rpow[b] = (int)((long)rpow[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (int)((a + (long)rpow[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int t = (int)((long)rpow[nb] * a % GM);
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ base darts
 * Left base vertices 0..NA-1, right base vertices NA..2NA-1.
 * Lift vertex id = base*GN + x. Dart e = (src, dst, label): (src,x) ~ (dst, x*label). */

static int NA;
static int ndart, npair;
static int dsrc[MAXDART], ddst[MAXDART], dpair[MAXDART], dpos[MAXDART];
static int lab[MAXDART], incLab[MAXDART];
static int pcnt[4], pu[4], pw[4], pdart[4][MAXD];
static int outD[2][MAXD], inD[4][MAXD];

static void setup_darts(int a, int p) {
    NA = a;
    int oc[4] = {0, 0, 0, 0}, ic[4] = {0, 0, 0, 0};
    ndart = 0;
    if (a == 1) {
        npair = 1;
        pu[0] = 0; pw[0] = 1; pcnt[0] = d;
    } else {
        npair = 4;
        pu[0] = 0; pw[0] = 2; pcnt[0] = p;
        pu[1] = 0; pw[1] = 3; pcnt[1] = d - p;
        pu[2] = 1; pw[2] = 2; pcnt[2] = d - p;
        pu[3] = 1; pw[3] = 3; pcnt[3] = p;
    }
    for (int pi = 0; pi < npair; pi++)
        for (int j = 0; j < pcnt[pi]; j++) {
            int e = ndart++;
            dsrc[e] = pu[pi];
            ddst[e] = pw[pi];
            dpair[e] = pi;
            dpos[e] = j;
            pdart[pi][j] = e;
            outD[pu[pi]][oc[pu[pi]]++] = e;
            inD[pw[pi]][ic[pw[pi]]++] = e;
        }
}

/* True if label x is used by a dart of pair pi at position j < limit, j != skip. */
static int taken(int pi, int x, int skip, int limit) {
    for (int j = 0; j < limit; j++)
        if (j != skip && lab[pdart[pi][j]] == x) return 1;
    return 0;
}

static void random_labels(void) {
    for (int pi = 0; pi < npair; pi++)
        for (int j = 0; j < pcnt[pi]; j++) {
            int x;
            do { x = rndint(GN); } while (taken(pi, x, -1, j));
            lab[pdart[pi][j]] = x;
        }
}

/* ------------------------------------------------------------ cost (diameter defect) */

static int vis[MAXV], que[MAXV];
static int stampc = 0;

/* Number of lift vertices reached from src within distance D. */
static int bfs_tail(int src) {
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int base = v / GN, x = v - base * GN;
            if (base < NA) {
                for (int j = 0; j < d; j++) {
                    int e = outD[base][j];
                    int u = ddst[e] * GN + gmul(x, lab[e]);
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            } else {
                for (int j = 0; j < d; j++) {
                    int e = inD[base][j];
                    int u = dsrc[e] * GN + gmul(x, ginv(lab[e]));
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each fibre, so one source per base
 * vertex suffices: cost 0 means diameter <= D. */
static long cost_eval(void) {
    int V = 2 * NA * GN;
    long c = 0;
    for (int s = 0; s < 2 * NA; s++) c += (long)(V - bfs_tail(s * GN));
    return c;
}

/* ------------------------------------------------------------ annealing */

static int anneal(double until) {
    const int iters = 3000;
    while (now() < until) {
        if (!have_inc) {
            random_labels();
        } else {
            memcpy(lab, incLab, sizeof(int) * (size_t)ndart);
            for (int t = 0; t < 2; t++) {
                int e = rndint(ndart), x;
                do { x = rndint(GN); } while (taken(dpair[e], x, dpos[e], pcnt[dpair[e]]));
                lab[e] = x;
            }
        }
        long cost = cost_eval();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have_inc ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(ndart), x;
            do { x = rndint(GN); } while (taken(dpair[e], x, dpos[e], pcnt[dpair[e]]));
            int old = lab[e];
            lab[e] = x;
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                lab[e] = old;
            }
        }
        if (cost == 0) return 1;
        if (!have_inc || cost < inc_cost) {
            have_inc = 1;
            inc_cost = cost;
            memcpy(incLab, lab, sizeof(int) * (size_t)ndart);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static Cand cand[MAXCAND];
static int ncand = 0;

/* All groups Z_m x|_r Z_k of order N with gcd(r,m) = 1 and r^k = 1 mod m. */
static void add_groups(int a, int N, int p, int T) {
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ncand < MAXCAND) {
                Cand c = {a, 1, k, 0, p, T};
                cand[ncand++] = c;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_i(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) {
                Cand c = {a, m, k, r, p, T};
                cand[ncand++] = c;
            }
        }
    }
}

static void print_solution(void) {
    int V = 2 * NA * GN;
    printf("%d %d\n", V, ndart * GN);
    for (int e = 0; e < ndart; e++)
        for (int x = 0; x < GN; x++)
            printf("%d %d\n", dsrc[e] * GN + x, ddst[e] * GN + gmul(x, lab[e]));
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > 4 * MAXN) hi = 4 * MAXN;
    if (lo < 2 * d) lo = 2 * d;

    /* Candidates in increasing total order T = 2*a*N. */
    for (int T = lo; T <= hi && ncand < MAXCAND; T++) {
        if (T % 2 == 0) {
            int N = T / 2;
            if (N >= d && N <= MAXN) add_groups(1, N, d, T);
        }
        if (T % 4 == 0) {
            int N = T / 4;
            if (N >= d && N <= MAXN)
                for (int p = 1; p <= d / 2; p++) add_groups(2, N, p, T);
        }
    }

    int best_T = 0, have_best = 0;
    for (int ci = 0; ci < ncand; ci++) {
        Cand c = cand[ci];
        if (c.T <= best_T) continue;
        double rem = t_end - now();
        if (rem < 0.2) break;
        double slice = 0.1 * rem;
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        setup_group(c.m, c.k, c.r);
        setup_darts(c.a, c.p);
        have_inc = 0;
        if (anneal(now() + slice)) {
            best_T = c.T;
            have_best = 1;
            bestCand = c;
            memcpy(bestLab, lab, sizeof(int) * (size_t)ndart);
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestCand.m, bestCand.k, bestCand.r);
    setup_darts(bestCand.a, bestCand.p);
    memcpy(lab, bestLab, sizeof(int) * (size_t)ndart);
    if (cost_eval() != 0) {
        printf("0 0\n");
        return 0;
    }
    print_solution();
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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

        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8, 2 * d)
        hi = min(mb, 4 * 4096)
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
