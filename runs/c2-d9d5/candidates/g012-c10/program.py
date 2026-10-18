"""Two-base-vertex voltage lifts over F_p x| Z_c for the bipartite degree-diameter problem.

Change from the parent: the search no longer uses only Haar graphs (one base vertex
per side). Each candidate is a voltage lift of a base graph with K = 2 vertices per
side. Its multiplicity matrix is [[a, d-a], [d-a, a]], with a voltage on every dart,
and the lift has 4N vertices. The group is F_p x| Z_c with p prime, so only mod-p
arithmetic is needed. Left translations act on each lift, so the diameter check
needs 4 BFS runs, one from each base vertex's identity lift. K = 1 (the Haar graph)
is kept as a sub-case so the search still covers the parent's family.

The C engine anneals over voltages, perturbing the incumbent between rounds. Python
keeps K_{d,d}, the projective-plane and generalized-quadrangle constructions, and
the Araujo-Lopez graph as validated fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Voltage lifts over F_p x| Z_c (p prime) with K = 1 or 2 base vertices per side.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the group order N = p*c. Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXDARTS 64
#define MAXCAND 40000

typedef struct { int q, c, N; } Cand;

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

/* ------------------------------------------------------------ prime field, group */

static int Q, C, N;
static int hval[MAXN];

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int is_prime(int x) {
    if (x < 2) return 0;
    for (long f = 2; f * f <= x; f++)
        if (x % f == 0) return 0;
    return 1;
}

static int prim_root(int q) {
    int fac[32], nf = 0, m = q - 1;
    for (int f = 2; (long)f * f <= m; f++)
        if (m % f == 0) {
            fac[nf++] = f;
            while (m % f == 0) m /= f;
        }
    if (m > 1) fac[nf++] = m;
    for (int g = 2; g < q; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g, (q - 1) / fac[i], q) == 1) ok = 0;
        if (ok) return g;
    }
    return -1;
}

/* Element (a, j) of F_q x| Z_c is coded a*C + j; (a,j)(b,t) = (a + h_j b, j + t),
 * where h_j = g^(j*(q-1)/c) has order dividing c. */
static void setup_group(int q, int c) {
    Q = q;
    C = c;
    N = q * c;
    int g = prim_root(q);
    long step = (q - 1) / c;
    for (int j = 0; j < c; j++) hval[j] = (int)powmod(g, (long)j * step, q);
}

static inline int gmul(int x, int y) {
    int a = x / C, j = x % C, b = y / C, t = y % C;
    int na = (a + hval[j] * b) % Q;
    int nt = (j + t) % C;
    return na * C + nt;
}

static int ginv(int x) {
    int a = x / C, j = x % C;
    int jn = (C - j) % C;
    int na = (int)(((long)(Q - a) % Q) * hval[jn] % Q);
    return na * C + jn;
}

/* ------------------------------------------------------------ voltage lift state */

static int K;                 /* base vertices per side: 1 or 2 */
static int nd;                /* number of darts: d (K=1) or 2d (K=2) */
static int bi[MAXDARTS], bj[MAXDARTS];
static int sv[MAXDARTS];
static int fw[MAXDARTS][MAXN], bw[MAXDARTS][MAXN];
static int adjA[2][MAXD], adjB[2][MAXD];

/* K=1: d darts from A0 to B0. K=2: multiplicities [[a, d-a], [d-a, a]]. */
static void init_darts(int KK, int a) {
    K = KK;
    int k = 0;
    if (K == 1) {
        for (int t = 0; t < d; t++) { bi[k] = 0; bj[k] = 0; k++; }
    } else {
        for (int t = 0; t < a; t++) { bi[k] = 0; bj[k] = 0; k++; }
        for (int t = 0; t < d - a; t++) { bi[k] = 0; bj[k] = 1; k++; }
        for (int t = 0; t < d - a; t++) { bi[k] = 1; bj[k] = 0; k++; }
        for (int t = 0; t < a; t++) { bi[k] = 1; bj[k] = 1; k++; }
    }
    nd = k;
    for (int i = 0; i < 2; i++) {
        int m = 0;
        for (int kk = 0; kk < nd; kk++)
            if (bi[kk] == i) adjA[i][m++] = kk;
    }
    for (int j = 0; j < 2; j++) {
        int m = 0;
        for (int kk = 0; kk < nd; kk++)
            if (bj[kk] == j) adjB[j][m++] = kk;
    }
}

static void set_v(int k, int x) {
    sv[k] = x;
    int xi = ginv(x);
    for (int g = 0; g < N; g++) {
        fw[k][g] = gmul(g, x);
        bw[k][g] = gmul(g, xi);
    }
}

static int same_block(int k, int kk) { return bi[k] == bi[kk] && bj[k] == bj[kk]; }

/* Parallel darts in one block need distinct voltages (keeps the lift simple). */
static int conflict_upto(int k, int x, int upto) {
    for (int kk = 0; kk < upto; kk++)
        if (kk != k && same_block(k, kk) && sv[kk] == x) return 1;
    return 0;
}
static int conflict_all(int k, int x) { return conflict_upto(k, x, nd); }

/* ------------------------------------------------------------ diameter cost */

static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;

/* Vertices: A_i(g) = i*N + g (i < K), B_j(h) = (K + j)*N + h.
 * Edge per dart k: A_{bi}(g) ~ B_{bj}(g * s_k). */
static int reach_count(int src) {
    int BOff = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BOff) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = adjA[i][t];
                    int u = BOff + bj[k] * N + fw[k][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BOff, j = w / N, h = w - j * N;
                for (int t = 0; t < d; t++) {
                    int k = adjB[j][t];
                    int u = bi[k] * N + bw[k][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms, so one identity lift per base vertex suffices. */
static long cover_cost(void) {
    long V = 2L * K * N;
    long c = 0;
    for (int r = 0; r < 2 * K; r++) c += V - reach_count(r * N);
    return c;
}

/* ------------------------------------------------------------ search */

static int found_K, found_a;
static int found_sv[MAXDARTS];

/* Iterated annealing over voltages. Fresh rounds draw K and a at random. Later
 * rounds perturb the incumbent (two voltages changed, same K and a).
 * Returns 1 on cost 0 (diameter <= D), 0 on timeout. */
static int search_group(double until, int allow1) {
    const int iters = 3000;
    const double Te = 0.3;
    int half = d / 2;
    int have = 0;
    long incost = 0;
    int incK = 2, inca = 1;
    int incv[MAXDARTS];
    while (now() < until) {
        int KK, a, fresh;
        fresh = (!have) || (rndint(3) == 0);
        if (fresh) {
            KK = (allow1 && rndint(2) == 0) ? 1 : 2;
            a = (KK == 1) ? 0 : 1 + rndint(half);
            init_darts(KK, a);
            for (int k = 0; k < nd; k++) {
                int x;
                do { x = rndint(N); } while (conflict_upto(k, x, k));
                set_v(k, x);
            }
        } else {
            KK = incK;
            a = inca;
            init_darts(KK, a);
            for (int k = 0; k < nd; k++) set_v(k, incv[k]);
            for (int t = 0; t < 2; t++) {
                int k = rndint(nd), x;
                do { x = rndint(N); } while (conflict_all(k, x));
                set_v(k, x);
            }
        }
        long cost = cover_cost();
        double c0 = (double)cost;
        double Ts = (fresh ? 0.15 : 0.05) * c0 + 2.0;
        long rbest = cost;
        int rv[MAXDARTS];
        memcpy(rv, sv, sizeof(int) * (size_t)nd);
        int timed = 0;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) { timed = 1; break; }
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(nd), x;
            do { x = rndint(N); } while (conflict_all(k, x));
            int old = sv[k];
            set_v(k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost < rbest) {
                    rbest = cost;
                    memcpy(rv, sv, sizeof(int) * (size_t)nd);
                }
            } else {
                set_v(k, old);
            }
        }
        if (cost == 0) {
            found_K = KK;
            found_a = a;
            memcpy(found_sv, sv, sizeof(int) * (size_t)nd);
            return 1;
        }
        if (!have || rbest < incost) {
            have = 1;
            incost = rbest;
            incK = KK;
            inca = a;
            memcpy(incv, rv, sizeof(int) * (size_t)nd);
        }
        if (timed) return 0;
    }
    return 0;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->q != y->q) return x->q < y->q ? -1 : 1;
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (hi < lo) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q <= hi; q++) {
        if (!is_prime(q)) continue;
        int cmax = hi / q;
        if (cmax > q - 1) cmax = q - 1;
        for (int c = 1; c <= cmax; c++) {
            if ((q - 1) % c) continue;
            long Nn = (long)q * c;
            if (Nn < lo || Nn > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].q = q;
                cand[nc].c = c;
                cand[nc].N = (int)Nn;
                nc++;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending group order. A candidate is only worth trying when its best total
     * 4N (or 2N for K = 1) can exceed the incumbent. */
    long bestTotal = 0;
    int hasBest = 0, bK = 0, ba = 0, bq = 0, bc = 0;
    static int bsv[MAXDARTS];
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (4L * cand[ci].N <= bestTotal) continue;
        double slice = 0.15 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].c);
        int allow1 = (2L * N > bestTotal);
        if (search_group(now() + slice, allow1)) {
            long tot = 2L * found_K * N;
            if (tot > bestTotal) {
                bestTotal = tot;
                hasBest = 1;
                bK = found_K;
                ba = found_a;
                bq = Q;
                bc = C;
                memcpy(bsv, found_sv, sizeof(int) * (size_t)(found_K == 1 ? d : 2 * d));
            }
        }
    }

    if (!hasBest) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bq, bc);
    init_darts(bK, ba);
    for (int k = 0; k < nd; k++) set_v(k, bsv[k]);
    int V = 2 * K * N;
    printf("%d %d\n", V, nd * N);
    for (int k = 0; k < nd; k++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", bi[k] * N + g, K * N + bj[k] * N + fw[k][g]);
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

    # Search: 2-base voltage lifts over F_p x| Z_c, with total order 4N (or 2N for K = 1).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.86 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 4 + 1, mb // 16)
        hi = mb // 4
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
