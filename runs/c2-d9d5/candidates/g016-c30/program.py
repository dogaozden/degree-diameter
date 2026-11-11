"""Multi-orbit group lifts for the bipartite degree-diameter problem.

Construction: pick a finite group G = Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1) of
order N and k_orb >= 2 orbits per side. Vertices are (side, orbit i, g) for g in G.
Each of the k_orb * d darts (i -> j, voltage s) joins (i, g) to (j, g s). Darts are
arranged as d random permutations of the orbits, so every orbit has out-degree d and
in-degree d. Darts sharing an (i, j) block get distinct voltages, so the graph is
simple, bipartite and d-regular, with 2 * k_orb * N vertices.

Left and right translations by G are automorphisms, so diameter <= D reduces to 2 * k_orb
BFS runs, one from each orbit representative on each side. The C engine tries
(group, k_orb) pairs in ascending order of order, anneals the dart pattern and voltages,
and keeps the largest success. Python keeps a valid fallback and checks the result.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit Z_m x|_r Z_k lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*k_orb*N.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 4
#define MAXD 32
#define MAXDARTS (MAXK * MAXD)
#define MAXN 8192
#define MAXV (2 * MAXK * MAXN)
#define MAXG 100000
#define MAXCAND 300000

typedef struct { int m, k, r; } Grp;
typedef struct { int V, korb, m, k, r; uint32_t key; } Cand;

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
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k
 * Element (a, b) coded as a*k + b. Product (a,b)(c,d) = (a + r^b c, b + d). */
static int GM, GK, GR, GN;
static int PW[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (int)(((long)a + (long)PW[b] * c) % GM);
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int c = (int)(((long)GM - ((long)PW[nb] * a) % GM) % GM);
    return c * GK + nb;
}

/* ------------------------------------------------------------ lift state */

static int KO, NDART;
static int fiD[MAXDARTS], tjD[MAXDARTS], blk[MAXDARTS], vol[MAXDARTS];
static int outD[MAXK][MAXD], inD[MAXK][MAXD];
static int fwd[MAXDARTS][MAXN], bwd[MAXDARTS][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart e joins left (fi, g) to right (tj, g s), so right (tj, h) joins left (fi, h s^-1). */
static void set_dart(int e, int s) {
    vol[e] = s;
    int si = ginv(s);
    for (int g = 0; g < GN; g++) {
        fwd[e][g] = gmul(g, s);
        bwd[e][g] = gmul(g, si);
    }
}

static void build_adj(void) {
    int co[MAXK], ci[MAXK];
    for (int i = 0; i < KO; i++) co[i] = ci[i] = 0;
    for (int e = 0; e < NDART; e++) {
        int i = fiD[e], j = tjD[e];
        outD[i][co[i]++] = e;
        inD[j][ci[j]++] = e;
    }
}

/* Random voltage for dart e, distinct from other darts in the same (i, j) block. */
static int pick_s(int e) {
    for (;;) {
        int s = rndint(GN), ok = 1;
        for (int f = 0; f < NDART && ok; f++)
            if (f != e && blk[f] == blk[e] && vol[f] == s) ok = 0;
        if (ok) return s;
    }
}

/* Random dart pattern: d random permutations of the KO orbits. Each left orbit
 * then has out-degree d and each right orbit in-degree d. */
static void setup_pattern(void) {
    NDART = KO * d;
    for (int t = 0; t < d; t++) {
        int p[MAXK];
        for (int i = 0; i < KO; i++) p[i] = i;
        for (int i = KO - 1; i > 0; i--) {
            int j = rndint(i + 1), tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
        for (int i = 0; i < KO; i++) {
            int e = t * KO + i;
            fiD[e] = i;
            tjD[e] = p[i];
            blk[e] = i * KO + p[i];
            vol[e] = -1;
        }
    }
    build_adj();
    for (int e = 0; e < NDART; e++) set_dart(e, pick_s(e));
}

/* Vertices: left (i, g) = i*GN + g; right (j, h) = KO*GN + j*GN + h. */
static int bfs_count(int src) {
    int L = KO * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < L) {
                int i = v / GN, g = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int e = outD[i][t];
                    int u = L + tjD[e] * GN + fwd[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int x = v - L;
                int j = x / GN, h = x - j * GN;
                for (int t = 0; t < d; t++) {
                    int e = inD[j][t];
                    int u = fiD[e] * GN + bwd[e][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over orbit representatives of unreached vertices. Zero means diameter <= D. */
static long cost_full(void) {
    int L = KO * GN, V = 2 * L;
    long c = 0;
    for (int i = 0; i < KO; i++) {
        c += V - bfs_count(i * GN);
        c += V - bfs_count(L + i * GN);
    }
    return c;
}

/* Annealing over dart voltages, with random restarts of the pattern. */
static int anneal(double until) {
    while (now() < until) {
        setup_pattern();
        long cost = cost_full();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 4000;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(NDART);
            int old = vol[e];
            int s = pick_s(e);
            set_dart(e, s);
            long c2 = cost_full();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_dart(e, old);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ best-so-far store */

static int bestVal = 0, bestM, bestK, bestR, bestKO, bestND;
static int bestFi[MAXDARTS], bestTj[MAXDARTS], bestVol[MAXDARTS];

static void save_best(const Cand *c) {
    bestVal = c->V;
    bestM = c->m;
    bestK = c->k;
    bestR = c->r;
    bestKO = KO;
    bestND = NDART;
    for (int e = 0; e < NDART; e++) {
        bestFi[e] = fiD[e];
        bestTj[e] = tjD[e];
        bestVol[e] = vol[e];
    }
}

static void print_best(void) {
    setup_group(bestM, bestK, bestR);
    KO = bestKO;
    NDART = bestND;
    for (int e = 0; e < NDART; e++) {
        fiD[e] = bestFi[e];
        tjD[e] = bestTj[e];
        blk[e] = fiD[e] * KO + tjD[e];
    }
    build_adj();
    for (int e = 0; e < NDART; e++) set_dart(e, bestVol[e]);
    int L = KO * GN;
    printf("%d %d\n", 2 * L, NDART * GN);
    for (int i = 0; i < KO; i++)
        for (int t = 0; t < d; t++) {
            int e = outD[i][t];
            for (int g = 0; g < GN; g++)
                printf("%d %d\n", i * GN + g, L + tjD[e] * GN + fwd[e][g]);
        }
}

static int cmpc(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

static Grp grp[MAXG];
static Cand cand[MAXCAND];

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
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (hi > MAXV) hi = MAXV;
    if (lo < 1) lo = 1;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    /* Groups whose order N can appear for some k_orb in [2, MAXK]. */
    long NloL = (lo + 2L * MAXK - 1) / (2L * MAXK);
    if (NloL < 2 * d) NloL = 2 * d;
    long NhiL = hi / 4;
    if (NhiL > MAXN) NhiL = MAXN;
    int ng = 0;
    for (int N = (int)NloL; N <= (int)NhiL && ng < MAXG; N++) {
        for (int m = 2; m <= N && ng < MAXG; m++) {
            if (N % m) continue;
            int k = N / m;
            if (k == 1) {
                grp[ng].m = m; grp[ng].k = 1; grp[ng].r = 1;
                ng++;
                continue;
            }
            for (int r = 1; r < m && ng < MAXG; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_l(r, k, m) != 1 % m) continue;
                grp[ng].m = m; grp[ng].k = k; grp[ng].r = r;
                ng++;
            }
        }
    }

    int nc = 0;
    for (int g = 0; g < ng && nc < MAXCAND; g++) {
        int N = grp[g].m * grp[g].k;
        for (int ko = 2; ko <= MAXK && nc < MAXCAND; ko++) {
            long V = 2L * ko * N;
            if (V < lo || V > hi) continue;
            cand[nc].V = (int)V;
            cand[nc].korb = ko;
            cand[nc].m = grp[g].m;
            cand[nc].k = grp[g].k;
            cand[nc].r = grp[g].r;
            cand[nc].key = (uint32_t)rnd();
            nc++;
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);

    /* Passes in ascending vertex count. Each attempt gets a fixed slice of the
     * budget. Candidates that failed are retried in later passes with fresh
     * random restarts. */
    double total = t_end - t0;
    double slice0 = total / 30.0;
    if (slice0 < 0.5) slice0 = 0.5;
    if (slice0 > 4.0) slice0 = 4.0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestVal) continue;
            double rem = t_end - now();
            if (rem < 0.2) break;
            tried = 1;
            double slice = slice0 < rem ? slice0 : rem;
            KO = cand[ci].korb;
            setup_group(cand[ci].m, cand[ci].k, cand[ci].r);
            if (anneal(now() + slice)) save_best(&cand[ci]);
        }
        if (!tried || t_end - now() < 0.2) break;
    }

    if (!bestVal) {
        printf("0 0\n");
        return 0;
    }
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

    # Multi-orbit group lifts: 2 * k_orb * N vertices, searched above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        hi = min(mb, 60000)
        lo = max(best[0] + 1, min(mb // 5, hi // 2))
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
