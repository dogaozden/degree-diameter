"""Multi-base voltage lifts over small groups for the bipartite degree-diameter problem.

Change of construction: the parent searched Haar graphs (one base edge pair) over
F_q x| H. This version searches general voltage lifts. The base is a d-regular
bipartite multigraph with a vertices per side (2 <= a <= 8). Its darts carry voltages
in a group G of order N (cyclic, or Z_m x| Z_k with r^k = 1 mod m). The lift has
2*a*N vertices and degree d. G acts by left multiplication on each fibre, so the
diameter is decided by one BFS from each base vertex (2a BFS runs). Simulated
annealing moves voltages and swaps dart targets, which keeps the B side regular.
Duplicate edges are penalised heavily.

Fallbacks: K_{d,d}, PG(2,q) incidence graphs, and the Araujo-Lopez graph.
Every returned graph is checked with lib.is_valid.
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

#define MAXD 64
#define MAXA 8
#define MAXAD (MAXA * MAXD)
#define MAXN 8192
#define MAXV 8192
#define MAXSPEC 200000
#define DUPPEN 10000000L

typedef struct { int a, m, k, r, N, total; } Spec;

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

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int ga, GM, GK, GR, GN, nd;
static int rp[MAXN];   /* rp[b] = r^b mod m */

/* Element (a, b) is coded a*k + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a1 = x / GK, b1 = x % GK;
    int c1 = y / GK, e1 = y % GK;
    int na = (a1 + rp[b1] * c1) % GM;
    int nb = (b1 + e1) % GK;
    return na * GK + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b), with r^(-b) = r^((k-b) mod k). */
static inline int ginv(int x) {
    int a1 = x / GK, b1 = x % GK;
    int nb = (GK - b1) % GK;
    int na = (int)((GM - ((long)rp[nb] * a1) % GM) % GM);
    return na * GK + nb;
}

static void setup_spec(Spec s) {
    ga = s.a;
    GM = s.m;
    GK = s.k;
    GR = s.r;
    GN = s.N;
    nd = ga * d;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * GR % GM);
}

/* ------------------------------------------------------------ lift state */

/* Dart idx = i*d + t goes from A_i to B_{tj[idx]} with voltage vo[idx].
 * Vertex A(i,x) = i*GN + x, B(j,y) = ga*GN + j*GN + y.
 * A(i,x) ~ B(j, x*v) for each dart (i, j, v). */
static int tj[MAXAD], vo[MAXAD], vinv[MAXAD], btj[MAXAD], bvo[MAXAD];
static int inD[MAXAD], icnt[MAXA];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void build_in(void) {
    for (int j = 0; j < ga; j++) icnt[j] = 0;
    for (int idx = 0; idx < nd; idx++) {
        int j = tj[idx];
        inD[j * d + icnt[j]] = idx;
        icnt[j]++;
        vinv[idx] = ginv(vo[idx]);
    }
}

static int count_dups(void) {
    int dup = 0;
    for (int i = 0; i < ga; i++)
        for (int t1 = 0; t1 < d; t1++)
            for (int t2 = 0; t2 < t1; t2++) {
                int x = i * d + t1, y = i * d + t2;
                if (tj[x] == tj[y] && vo[x] == vo[y]) dup++;
            }
    return dup;
}

/* Number of vertices NOT within distance D of src. */
static int bfs_unreached(int src) {
    int A = ga * GN, V = 2 * A;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < A) {
                int i = v / GN, x = v % GN;
                for (int t = 0; t < d; t++) {
                    int idx = i * d + t;
                    int u = A + tj[idx] * GN + gmul(x, vo[idx]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - A, j = w / GN, y = w % GN;
                for (int t = 0; t < d; t++) {
                    int idx = inD[j * d + t];
                    int u = (idx / d) * GN + gmul(y, vinv[idx]);
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return V - tail;
}

/* Cost 0 iff the lift is simple and has diameter <= D. Vertex transitivity on each
 * fibre means one BFS per base vertex (A side and B side) decides the diameter. */
static long eval_cost(void) {
    build_in();
    int dup = count_dups();
    if (dup) return DUPPEN * (long)dup;
    int A = ga * GN;
    long c = 0;
    for (int i = 0; i < ga; i++) c += bfs_unreached(i * GN);
    for (int j = 0; j < ga; j++) c += bfs_unreached(A + j * GN);
    return c;
}

static void random_init(void) {
    int slots[MAXAD];
    int p = 0;
    for (int j = 0; j < ga; j++)
        for (int t = 0; t < d; t++) slots[p++] = j;
    /* Each B vertex gets exactly d darts, so B is regular. */
    for (int i = nd - 1; i > 0; i--) {
        int r = rndint(i + 1);
        int tmp = slots[i]; slots[i] = slots[r]; slots[r] = tmp;
    }
    for (int idx = 0; idx < nd; idx++) {
        tj[idx] = slots[idx];
        vo[idx] = rndint(GN);
    }
}

/* Time-scheduled annealing on one group. Returns 1 when cost 0 is reached. */
static int search_spec(double until) {
    int tries = 0;
    do { random_init(); } while (count_dups() > 0 && ++tries < 2000);
    if (count_dups() > 0) return 0;
    long cost = eval_cost();
    if (cost == 0) return 1;
    double ts = now();
    double span = until - ts;
    if (span <= 0) return 0;
    double c0 = (double)cost;
    double Ts = 0.05 * c0 + 2.0, Te = 0.2;
    double frac = 0.0;
    for (long it = 0; ; it++) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= until) return 0;
            frac = (tn - ts) / span;
        }
        double T = Ts * pow(Te / Ts, frac);
        long c2;
        if (rnd01() < 0.5) {
            int idx = rndint(nd);
            int old = vo[idx];
            int nv = rndint(GN);
            if (nv == old) continue;
            vo[idx] = nv;
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else vo[idx] = old;
        } else {
            int x = rndint(nd), y = rndint(nd);
            if (x == y || tj[x] == tj[y]) continue;
            int tmp = tj[x]; tj[x] = tj[y]; tj[y] = tmp;
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = tj[x]; tj[x] = tj[y]; tj[y] = tmp; }
        }
        if (cost == 0) return 1;
    }
}

static int cmp_spec(const void *p, const void *q) {
    const Spec *x = p, *y = q;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
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
    t_end = t0 + limit * 0.95 - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (hi > MAXV) hi = MAXV;
    if (lo < 4) lo = 4;
    if (lo > hi) { printf("0 0\n"); return 0; }

    static Spec specs[MAXSPEC];
    int nspec = 0;
    for (int a = 2; a <= MAXA; a++) {
        int nlo = (lo + 2 * a - 1) / (2 * a);
        int nhi = hi / (2 * a);
        if (nlo < 2) nlo = 2;
        for (int N = nlo; N <= nhi && nspec < MAXSPEC; N++) {
            Spec cy = {a, N, 1, 1, N, 2 * a * N};
            specs[nspec++] = cy;
            for (int k = 2; k <= N / 2 && nspec < MAXSPEC; k++) {
                if (N % k) continue;
                int m = N / k;
                if (m < 2) continue;
                int got = 0, start = rndint(m);
                for (int t = 0; t < m && got < 2 && nspec < MAXSPEC; t++) {
                    int r = (start + t) % m;
                    if (r == 0 || gcdi(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1 % m) continue;
                    Spec sp = {a, m, k, r, N, 2 * a * N};
                    specs[nspec++] = sp;
                    got++;
                }
            }
        }
    }
    if (nspec == 0) { printf("0 0\n"); return 0; }
    qsort(specs, (size_t)nspec, sizeof(Spec), cmp_spec);

    int bestTotal = lo - 1;
    int found = 0;
    Spec bestSp = specs[0];
    int ptr = 0;
    while (1) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        while (ptr < nspec && specs[ptr].total <= bestTotal) ptr++;
        if (ptr >= nspec) break;
        /* Try specs in a band just above the current best, chosen at random. */
        int band = bestTotal / 25 + 40;
        int end = ptr;
        while (end < nspec && specs[end].total <= bestTotal + band) end++;
        if (end == ptr) end = ptr + 1;
        int pick = ptr + rndint(end - ptr);
        setup_spec(specs[pick]);
        double slice = 0.1 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (search_spec(now() + slice)) {
            bestTotal = specs[pick].total;
            bestSp = specs[pick];
            found = 1;
            memcpy(btj, tj, sizeof(int) * (size_t)nd);
            memcpy(bvo, vo, sizeof(int) * (size_t)nd);
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    setup_spec(bestSp);
    int A = ga * GN;
    printf("%d %d\n", 2 * A, nd * GN);
    for (int idx = 0; idx < nd; idx++) {
        int i = idx / d;
        for (int x = 0; x < GN; x++) {
            int y = gmul(x, bvo[idx]);
            printf("%d %d\n", i * GN + x, A + btj[idx] * GN + y);
        }
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

    # Search: multi-base voltage lifts over small groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8)
        hi = min(mb // 3, 8000)
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
