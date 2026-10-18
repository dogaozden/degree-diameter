"""Multi-vertex voltage bi-lifts over metacyclic groups for the bipartite degree-diameter problem.

The parent searched Haar graphs (one vertex per side) over affine groups. This version
changes the construction. The base graph has B vertices per side and is d-regular: its
darts form d permutations of {0..B-1}, and each dart carries a label in a metacyclic
group G = Z_m x|_r Z_k. Dart (t, i) joins L(i, x) to R(sigma_t(i), x*g). Left
multiplication by G is an automorphism that acts transitively on each side fiber, so
the diameter check needs only 2B BFS runs, from L(i, e) and R(j, e).

The order is 2*B*|G|, so this family reaches orders the single-vertex Haar lifts miss
(for example 2*2*N with N near 628). Simulated annealing over labels and permutations
minimizes unreached pairs plus a penalty for duplicate edges. The Python fallbacks
(projective planes, Araujo-Lopez, W(q), K_{d,d}) are kept and every result is checked.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage bi-lift search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit minV maxV     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXB 4
#define MAXDART 160
#define MAXVTX (2 * MAXB * MAXN)
#define MAXG 4096
#define MAXCAND 40000
#define MAXPERM 24

typedef struct { int m, k, r; } Grp;
typedef struct { int b, N, V; } Cand;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ groups */

static Grp GL[MAXG];
static int ngrp = 0;
static int enum_N = -1;

/* All groups Z_m x|_r Z_k of order N = m*k with gcd(r,m)=1 and r^k = 1 mod m. */
static void enum_groups(int N) {
    if (N == enum_N) return;
    enum_N = N;
    ngrp = 0;
    for (int k = 1; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        if (m == 1) {
            if (ngrp < MAXG) { GL[ngrp].m = 1; GL[ngrp].k = k; GL[ngrp].r = 0; ngrp++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1) continue;
            if (ngrp < MAXG) { GL[ngrp].m = m; GL[ngrp].k = k; GL[ngrp].r = r; ngrp++; }
        }
    }
}

static int GM, GK, GN, GR;
static int RP[MAXN];
static Grp curG;

static void set_group(Grp g) {
    curG = g;
    GM = g.m;
    GK = g.k;
    GN = g.m * g.k;
    GR = g.r;
    RP[0] = 1 % GM;
    for (int b = 1; b < GK; b++) RP[b] = (int)((long)RP[b - 1] * GR % GM);
}

/* Element (a, b) is coded a*GK + b. Product (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + (RP[b] * c) % GM) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

/* Inverse of (a, b) is (-r^(-b) a, -b) = (-r^nb a, nb) with nb = -b mod k. */
static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - (RP[nb] * a) % GM) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ permutations */

static int PERMS[MAXPERM][MAXB];
static int NPERM = 0;
static int permB = -1;

static int next_perm(int *a, int n) {
    int i = n - 2;
    while (i >= 0 && a[i] > a[i + 1]) i--;
    if (i < 0) return 0;
    int j = n - 1;
    while (a[j] < a[i]) j--;
    int t = a[i]; a[i] = a[j]; a[j] = t;
    for (int l = i + 1, r = n - 1; l < r; l++, r--) {
        t = a[l]; a[l] = a[r]; a[r] = t;
    }
    return 1;
}

static void build_perms(int Bv) {
    if (Bv == permB) return;
    permB = Bv;
    int a[MAXB];
    for (int i = 0; i < Bv; i++) a[i] = i;
    NPERM = 0;
    do {
        for (int i = 0; i < Bv; i++) PERMS[NPERM][i] = a[i];
        NPERM++;
    } while (next_perm(a, Bv));
}

/* ------------------------------------------------------------ lift state */

/* Darts e = t*B + i, t in 0..d-1, i in 0..B-1. Dart e joins left i to right
 * rj[e] = PERMS[pidx[t]][i] through label lab[e]. Each side has d darts per vertex. */
static int B, NDART;
static int lab[MAXDART], pidx[MAXDART], rj[MAXDART];
static int RL[MAXB][MAXDART];
static int FW[MAXDART][MAXN], BW[MAXDART][MAXN];
static int vis[MAXVTX], que[MAXVTX];
static int stamp_ = 0;

static void set_rows(int t) {
    for (int i = 0; i < B; i++) rj[t * B + i] = PERMS[pidx[t]][i];
}

static void rebuild_RL(void) {
    for (int j = 0; j < B; j++) {
        int c = 0;
        for (int e = 0; e < NDART; e++)
            if (rj[e] == j && c < MAXDART) RL[j][c++] = e;
    }
}

static void update_dart(int e) {
    int g = lab[e];
    int gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        FW[e][x] = gmul(x, g);
        BW[e][x] = gmul(x, gi);
    }
}

/* Vertices: left (i, x) = i*GN + x; right (j, y) = B*GN + j*GN + y. */
static int bfs_reach(int src) {
    int LN = B * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < LN) {
                int i = v / GN, x = v % GN;
                for (int t = 0; t < d; t++) {
                    int e = t * B + i;
                    int u = LN + rj[e] * GN + FW[e][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - LN;
                int j = w / GN, y = w % GN;
                for (int t = 0; t < d; t++) {
                    int e = RL[j][t];
                    int u = (e % B) * GN + BW[e][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

static long dup_count(void) {
    long c = 0;
    for (int e1 = 0; e1 < NDART; e1++)
        for (int e2 = e1 + 1; e2 < NDART; e2++)
            if (e1 % B == e2 % B && rj[e1] == rj[e2] && lab[e1] == lab[e2]) c++;
    return c;
}

/* Cost 0 means diameter <= D and simple. Fibers are orbits of the left G-action,
 * so BFS from one representative per fiber on each side covers all pairs. */
static long eval_cost(void) {
    int V = 2 * B * GN;
    long c = 0;
    for (int i = 0; i < B; i++) {
        c += V - bfs_reach(i * GN);
        c += V - bfs_reach(B * GN + i * GN);
    }
    c += 4 * dup_count();
    return c;
}

/* ------------------------------------------------------------ search */

static int bestFound = 0, bestB = 0;
static Grp bestG;
static int bestLab[MAXDART], bestPidx[MAXDART];

static int setup_cell(int Bv, int N) {
    B = Bv;
    NDART = d * B;
    build_perms(B);
    enum_groups(N);
    return ngrp;
}

/* Simulated annealing over labels and permutations for random groups of the cell.
 * Returns 1 on cost 0 (valid graph), 0 on timeout. */
static int search_cell(double until) {
    const int iters = 6000;
    while (now() < until) {
        Grp g = GL[rndint(ngrp)];
        set_group(g);
        for (int e = 0; e < NDART; e++) lab[e] = rndint(GN);
        for (int t = 0; t < d; t++) pidx[t] = rndint(NPERM);
        for (int t = 0; t < d; t++) set_rows(t);
        rebuild_RL();
        for (int e = 0; e < NDART; e++) update_dart(e);
        long cost = eval_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (NPERM == 1 || rnd01() < 0.85) {
                int e = rndint(NDART);
                int old = lab[e];
                int nl = rndint(GN);
                if (nl == old) continue;
                lab[e] = nl;
                update_dart(e);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    lab[e] = old;
                    update_dart(e);
                }
            } else {
                int t = rndint(d);
                int oldp = pidx[t];
                int np = rndint(NPERM);
                if (np == oldp) continue;
                pidx[t] = np;
                set_rows(t);
                rebuild_RL();
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    pidx[t] = oldp;
                    set_rows(t);
                    rebuild_RL();
                }
            }
        }
        if (cost == 0) {
            bestFound = 1;
            bestB = B;
            bestG = curG;
            memcpy(bestLab, lab, sizeof(lab));
            memcpy(bestPidx, pidx, sizeof(pidx));
            return 1;
        }
    }
    return 0;
}

static void emit(void) {
    B = bestB;
    NDART = d * B;
    build_perms(B);
    set_group(bestG);
    for (int e = 0; e < NDART; e++) lab[e] = bestLab[e];
    for (int t = 0; t < d; t++) pidx[t] = bestPidx[t];
    for (int t = 0; t < d; t++) set_rows(t);
    int LN = B * GN;
    printf("%d %d\n", 2 * LN, NDART * GN);
    for (int e = 0; e < NDART; e++) {
        int i = e % B;
        for (int x = 0; x < GN; x++)
            printf("%d %d\n", i * GN + x, LN + rj[e] * GN + gmul(x, lab[e]));
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->b - y->b;
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
    long minV = atol(argv[5]);
    long maxV = atol(argv[6]);
    t_end = now() + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > 32 || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (minV < 1) minV = 1;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int b = 1; b <= MAXB; b++) {
        if (b * d > MAXDART) break;
        long loN = (minV + 2L * b - 1) / (2L * b);
        if (loN < d) loN = d;
        long hiN = maxV / (2L * b);
        if (hiN > MAXN) hiN = MAXN;
        for (long N = loN; N <= hiN && nc < MAXCAND; N++) {
            cand[nc].b = b;
            cand[nc].N = (int)N;
            cand[nc].V = (int)(2 * b * N);
            nc++;
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestV = minV - 1;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.12 * rem;
            if (slice < 0.6) slice = 0.6;
            if (slice > rem) slice = rem;
            setup_cell(cand[ci].b, cand[ci].N);
            if (search_cell(now() + slice)) bestV = cand[ci].V;
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!bestFound) {
        printf("0 0\n");
        return 0;
    }
    emit();
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

    # Search: multi-vertex voltage bi-lifts over metacyclic groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        minV = best[0] + 1
        maxV = min(mb, int(best[0] * 1.2) + 2)
        if budget > 2.0 and minV <= maxV:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), minV, maxV],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
