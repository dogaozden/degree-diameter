"""Multi-orbit group lifts for the bipartite degree-diameter problem.

Construction: pick a group G of order N (cyclic Z_m, or F_q x| H with q prime and H of
order c dividing q-1), a base "circulant" block matrix with b in {1,2,3} left and right
orbits (block multiplicities w_0..w_{b-1} summing to d), and group elements for every
dart. Left vertices L_{i,g} and right vertices R_{j,h} (2bN in total) are joined by
L_{i,g} ~ R_{j,g*s} for each dart (i -> j, s). The graph is d-regular, bipartite and
simple, and left multiplication is an automorphism. So diameter <= D reduces to BFS
from one representative per orbit (2b BFS runs).

The C engine searches the candidates in ascending order of order n = 2bN, with simulated
annealing on the dart elements. Successes raise the bar. Later passes give each candidate
a larger time slice and retry it. Python keeps a valid fallback and verifies the result.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 3
#define MAXD 32
#define MAXDART 96
#define MAXN 5000
#define MAXV 32768
#define MAXCAND 60000
#define MAXCFG 1024
#define MAXQ 1300
#define MAXC 1400
#define MAXAG 8192

typedef struct { int b, w0, w1, w2, gtype, gp1, gp2, N, n; } Cand;
typedef struct { int b, w0, w1, w2; } Cfg;

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

/* ------------------------------------------------------------ groups */

static int gtype, GN, GQ, GC;
static int hv[MAXC];

static long powmod(long a, long e, long m) {
    long r = 1 % m;
    a %= m;
    while (e > 0) {
        if (e & 1) r = r * a % m;
        a = a * a % m;
        e >>= 1;
    }
    return r;
}

/* gtype 0: cyclic Z_m. gtype 1: F_q x| H, element (a, h_j) coded as a*c + j,
 * h_j = r^j with r of order c in F_q^*, product (a,h_j)(b,h_t) = (a + h_j b, h_{j+t}). */
static void setup_group(const Cand *cd) {
    gtype = cd->gtype;
    if (gtype == 0) {
        GN = cd->gp1;
        GQ = 0;
        GC = 1;
        return;
    }
    GQ = cd->gp1;
    GC = cd->gp2;
    GN = GQ * GC;
    int q = GQ, c = GC, r = 1;
    for (int x = 2; x < q; x++) {
        long y = powmod(x, (q - 1) / c, q);
        long z = y;
        int ord = 1;
        while (z != 1 && ord <= c) {
            z = z * y % q;
            ord++;
        }
        if (z == 1 && ord == c) {
            r = (int)y;
            break;
        }
    }
    hv[0] = 1;
    for (int j = 1; j < c; j++) hv[j] = (int)((long)hv[j - 1] * r % q);
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    int a = x / GC, j = x - (x / GC) * GC;
    int bb = y / GC, t = y - (y / GC) * GC;
    long na = ((long)a + (long)hv[j] * bb) % GQ;
    int nj = j + t;
    if (nj >= GC) nj -= GC;
    return (int)(na * GC + nj);
}

static inline int ginv(int x) {
    if (gtype == 0) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    long na = (GQ - ((long)a * hv[jn]) % GQ) % GQ;
    return (int)(na * GC + jn);
}

/* ------------------------------------------------------------ lift state */

static int b_, N_, BN_, NDART;
static int dsrc[MAXDART], ddst[MAXDART], dblk[MAXDART];
static int ldart[MAXB][MAXD], rdart[MAXB][MAXD];
static int elem[MAXDART];
static int fwd[MAXDART][MAXN], bwd[MAXDART][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void setup_config(const Cand *cd) {
    int b = cd->b;
    int w[MAXB];
    w[0] = cd->w0;
    w[1] = cd->w1;
    w[2] = cd->w2;
    b_ = b;
    N_ = cd->N;
    BN_ = b * N_;
    NDART = 0;
    int lc[MAXB], rc[MAXB];
    for (int i = 0; i < MAXB; i++) lc[i] = rc[i] = 0;
    for (int i = 0; i < b; i++)
        for (int j = 0; j < b; j++) {
            int mult = w[((j - i) % b + b) % b];
            for (int t = 0; t < mult; t++) {
                dsrc[NDART] = i;
                ddst[NDART] = j;
                dblk[NDART] = i * b + j;
                ldart[i][lc[i]++] = NDART;
                rdart[j][rc[j]++] = NDART;
                NDART++;
            }
        }
}

/* Dart k joins L_{src,g} to R_{dst,g*x}. */
static void set_dart(int k, int x) {
    elem[k] = x;
    int xi = ginv(x);
    for (int g = 0; g < N_; g++) fwd[k][g] = gmul(g, x);
    for (int h = 0; h < N_; h++) bwd[k][h] = gmul(h, xi);
}

/* Vertices: L_{i,g} = i*N + g, R_{j,h} = BN + j*N + h. */
static int bfs_count(int src) {
    int N = N_, BN = BN_;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = ldart[i][t];
                    int u = BN + ddst[k] * N + fwd[k][g];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int r = v - BN;
                int j = r / N, h = r - j * N;
                for (int t = 0; t < d; t++) {
                    int k = rdart[j][t];
                    int u = dsrc[k] * N + bwd[k][h];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Every orbit is a regular G-orbit, so the representatives L_{i,e} and R_{j,e} suffice. */
static long cover_cost(void) {
    long V = 2L * BN_, cost = 0;
    for (int i = 0; i < b_; i++) cost += V - bfs_count(i * N_);
    for (int j = 0; j < b_; j++) cost += V - bfs_count(BN_ + j * N_);
    return cost;
}

static void random_init(void) {
    for (int k = 0; k < NDART; k++) {
        int x;
        for (;;) {
            x = rndint(N_);
            int ok = 1;
            for (int k2 = 0; k2 < k; k2++)
                if (dblk[k2] == dblk[k] && elem[k2] == x) {
                    ok = 0;
                    break;
                }
            if (ok) break;
        }
        set_dart(k, x);
    }
}

/* Simulated annealing over dart elements. Returns 1 on cost 0, leaving the state in elem[]. */
static int run_sa(double until) {
    const int iters = 4000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(NDART);
            int x = rndint(N_);
            if (x == elem[k]) continue;
            int bad = 0;
            for (int k2 = 0; k2 < NDART; k2++)
                if (k2 != k && dblk[k2] == dblk[k] && elem[k2] == x) {
                    bad = 1;
                    break;
                }
            if (bad) continue;
            int old = elem[k];
            set_dart(k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(k, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b_p) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b_p;
    if (x->n != y->n) return x->n < y->n ? -1 : 1;
    if (x->b != y->b) return x->b < y->b ? -1 : 1;
    return 0;
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
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    /* Block configurations: circulant multiplicities w with sum d. */
    static Cfg cfgs[MAXCFG];
    int ncfg = 0;
    cfgs[ncfg].b = 1; cfgs[ncfg].w0 = d; cfgs[ncfg].w1 = 0; cfgs[ncfg].w2 = 0; ncfg++;
    for (int a = 1; a <= d / 2 && ncfg < MAXCFG; a++) {
        cfgs[ncfg].b = 2; cfgs[ncfg].w0 = a; cfgs[ncfg].w1 = d - a; cfgs[ncfg].w2 = 0; ncfg++;
    }
    for (int w0 = 1; w0 <= d; w0++)
        for (int w1 = 0; w1 <= w0; w1++)
            for (int w2 = 0; w2 <= w0; w2++)
                if (w0 + w1 + w2 == d && ncfg < MAXCFG) {
                    cfgs[ncfg].b = 3; cfgs[ncfg].w0 = w0; cfgs[ncfg].w1 = w1; cfgs[ncfg].w2 = w2;
                    ncfg++;
                }

    /* Affine groups: prime q, c | q-1, c >= 2. */
    static int ag_q[MAXAG], ag_c[MAXAG];
    int nag = 0;
    for (int q = 3; q < MAXQ; q++) {
        int isp = 1;
        for (int f = 2; f * f <= q; f++)
            if (q % f == 0) {
                isp = 0;
                break;
            }
        if (!isp) continue;
        for (int c = 2; c <= q - 1; c++)
            if ((q - 1) % c == 0 && (long)q * c <= MAXN && nag < MAXAG) {
                ag_q[nag] = q;
                ag_c[nag] = c;
                nag++;
            }
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int ci = 0; ci < ncfg; ci++) {
        Cfg f = cfgs[ci];
        int b = f.b;
        int maxw = f.w0;
        if (f.w1 > maxw) maxw = f.w1;
        if (f.w2 > maxw) maxw = f.w2;
        for (long m = 2; m <= MAXN; m++) {
            long n = 2L * b * m;
            if (n > hi || n > MAXV) break;
            if (n <= lo || m < maxw) continue;
            if (nc < MAXCAND) {
                Cand *c = &cand[nc++];
                c->b = b; c->w0 = f.w0; c->w1 = f.w1; c->w2 = f.w2;
                c->gtype = 0; c->gp1 = (int)m; c->gp2 = 0;
                c->N = (int)m; c->n = (int)n;
            }
        }
        for (int t = 0; t < nag; t++) {
            long N = (long)ag_q[t] * ag_c[t];
            long n = 2L * b * N;
            if (n <= lo || n > hi || n > MAXV) continue;
            if (N < maxw) continue;
            if (nc < MAXCAND) {
                Cand *c = &cand[nc++];
                c->b = b; c->w0 = f.w0; c->w1 = f.w1; c->w2 = f.w2;
                c->gtype = 1; c->gp1 = ag_q[t]; c->gp2 = ag_c[t];
                c->N = (int)N; c->n = (int)n;
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestn = lo;
    int best_idx = -1;
    static int bestElem[MAXDART];

    /* Passes over candidates in ascending n. Slices grow with each pass. */
    for (int pass = 0; pass < 60; pass++) {
        int tried = 0;
        double mult = (double)(1 << (pass < 12 ? pass : 12));
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].n <= bestn) continue;
            double rem = t_end - now();
            if (rem < 0.2) break;
            tried = 1;
            double slice = 0.03 * rem * mult;
            if (slice < 0.3) slice = 0.3;
            if (slice > rem) slice = rem;
            setup_group(&cand[ci]);
            setup_config(&cand[ci]);
            if (run_sa(now() + slice)) {
                bestn = cand[ci].n;
                best_idx = ci;
                memcpy(bestElem, elem, sizeof(int) * (size_t)NDART);
            }
        }
        if (!tried || t_end - now() < 0.2) break;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand *bc = &cand[best_idx];
    setup_group(bc);
    setup_config(bc);
    for (int k = 0; k < NDART; k++) set_dart(k, bestElem[k]);
    int N = N_, BN = BN_;
    printf("%d %ld\n", 2 * BN, (long)BN * d);
    for (int i = 0; i < b_; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++) {
                int k = ldart[i][t];
                printf("%d %d\n", i * N + g, BN + ddst[k] * N + fwd[k][g]);
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

    # Search: multi-orbit group lifts (b = 1, 2, 3 orbits per side) over cyclic and
    # affine groups, with orders above the current best and below the Moore bound.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0], mb // 4)
        hi = mb
        if budget > 2.0 and lo < hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
