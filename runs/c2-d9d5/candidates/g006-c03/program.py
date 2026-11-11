"""Multi-fibre group lifts for the bipartite degree-diameter problem.

Construction (new in this version): a base bipartite multigraph with K vertices per
side and d layers. Layer t is a permutation sig[t] (A_i -> B_{sig[t][i]}), and every
dart (t, i) carries a voltage g in G = Z_m x|_r Z_k2. The lift has vertices A_i x g and
B_j x g (g in G) and edges (A_i, x) ~ (B_{sig[t][i]}, x*g_{t,i}) for all t. This graph is
d-regular up to duplicate darts, which are removed before output, and bipartite.

Left multiplication by G is an automorphism, so every vertex is equivalent to one of the
2K fibre representatives (A_i, e) and (B_j, e). Diameter <= D therefore reduces to 2K
bounded BFS runs. The search is simulated annealing over voltages and base permutations,
with cost equal to the number of uncovered (source, vertex) pairs. The group order and
base size are chosen by binary search over the admissible (K, group) candidates in a
window below the Moore bound.

The earlier affine Haar search is kept as a special case (K = 1, semidirect groups
Z_p x| Z_c). Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the
K_{d,d} fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-fibre voltage lift search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 8
#define MAXD 32
#define MAXN 4096
#define MAXCAND 200000

typedef struct { int K, m, k2, r, N; } Cand;

static int d, D, K, GN;
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

/* ------------------------------------------------------------ group Z_m x|_r Z_k2 */

static int gm, gk, gr;
static int rp[MAXN];

/* Element (a, b) is coded a*k2 + b. Product: (a,b)(c,e) = (a + r^b c, b + e). */
static void setup_group(int m, int k2, int r) {
    gm = m;
    gk = k2;
    gr = r;
    GN = m * k2;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)(((long)rp[b - 1] * r) % m);
}

static inline int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    int na = (a + rp[b] * c) % gm;
    int nb = (b + e) % gk;
    return na * gk + nb;
}

static int ginv(int x) {
    int a = x / gk, b = x % gk;
    int nb = (gk - b) % gk;
    int na = (int)((gm - ((long)rp[nb] * a) % gm) % gm);
    return na * gk + nb;
}

/* ------------------------------------------------------------ lift state */

static int sig[MAXD][MAXK];      /* sig[t][i]: B-fibre hit by A-fibre i in layer t */
static int isig[MAXD][MAXK];     /* isig[t][j]: the i with sig[t][i] = j */
static int gv[MAXD][MAXK];       /* voltage of dart (t, i) */
static int mulR[MAXD][MAXK][MAXN];   /* x -> x * g */
static int mulRi[MAXD][MAXK][MAXN];  /* y -> y * g^-1 */
static int bestSig[MAXD][MAXK], bestGv[MAXD][MAXK];

static void set_volt(int t, int i) {
    int g = gv[t][i], gi = ginv(g);
    for (int x = 0; x < GN; x++) {
        mulR[t][i][x] = gmul(x, g);
        mulRi[t][i][x] = gmul(x, gi);
    }
}

static void init_random(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) sig[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = sig[t][i];
            sig[t][i] = sig[t][j];
            sig[t][j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            isig[t][sig[t][i]] = i;
            gv[t][i] = rndint(GN);
            set_volt(t, i);
        }
    }
}

/* Swap the targets of A-fibres i1 and i2 in layer t. Applying it twice is the identity. */
static void swap_perm(int t, int i1, int i2) {
    int tmp = sig[t][i1];
    sig[t][i1] = sig[t][i2];
    sig[t][i2] = tmp;
    isig[t][sig[t][i1]] = i1;
    isig[t][sig[t][i2]] = i2;
}

/* ------------------------------------------------------------ BFS and cost */

/* Vertices: A_i,x = i*GN + x; B_j,y = K*GN + j*GN + y.
 * A_i,x ~ B_{sig[t][i]}, x*g_{t,i};  B_j,y ~ A_{isig[t][j]}, y*g^-1. */
static int vis[2 * MAXK * MAXN], que[2 * MAXK * MAXN];
static int stamp_ = 0;

static int reach_count(int src) {
    int KN = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int u = KN + sig[t][i] * GN + mulR[t][i][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KN, j = w / GN, y = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int i = isig[t][j];
                    int u = i * GN + mulRi[t][i][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sources (A_i, e) and (B_j, e) cover all vertex orbits under left translation. */
static long cover_cost(void) {
    int V = 2 * K * GN;
    long c = 0;
    for (int i = 0; i < K; i++) {
        c += (long)(V - reach_count(i * GN));
        c += (long)(V - reach_count(K * GN + i * GN));
    }
    return c;
}

/* ------------------------------------------------------------ annealing */

/* Returns 1 with the solution left in sig/gv when cost 0 is reached, 0 on timeout. */
static int anneal(double until) {
    const int iters = 6000;
    while (now() < until) {
        init_random();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (K >= 2 && rnd01() < 0.4) {
                int t = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                swap_perm(t, i1, i2);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else swap_perm(t, i1, i2);
            } else {
                int t = rndint(d), i = rndint(K);
                int old = gv[t][i];
                gv[t][i] = rndint(GN);
                set_volt(t, i);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else { gv[t][i] = old; set_volt(t, i); }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

static void add_cand(int KK, int m, int k2, int r) {
    if (nc < MAXCAND) {
        Cand c = {KK, m, k2, r, m * k2};
        cand[nc++] = c;
    }
}

/* Every K in 1..MAXK, every group Z_m x|_r Z_k2 with m*k2 = N and 2*K*N in [lo, hi].
 * Up to 3 non-trivial r per (m, k2); r = 1 (abelian) only when nothing else exists. */
static void gen_cands(long lo, long hi) {
    for (int KK = 1; KK <= MAXK; KK++) {
        long Nlo = (lo + 2L * KK - 1) / (2L * KK);
        long Nhi = hi / (2L * KK);
        if (Nlo < 1) Nlo = 1;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long N = Nlo; N <= Nhi; N++) {
            for (long m = 1; m <= N; m++) {
                if (N % m) continue;
                long k2 = N / m;
                int cnt = 0, have1 = 0;
                for (long r = 0; r < m && cnt < 3; r++) {
                    if (gcdl(r, m) != 1) continue;
                    if (powmod(r, k2, m) != 1 % m) continue;
                    if (r == 1) { have1 = 1; continue; }
                    add_cand(KK, (int)m, (int)k2, (int)r);
                    cnt++;
                }
                if (cnt == 0 && have1) add_cand(KK, (int)m, (int)k2, 1);
            }
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    long tx = 2L * x->K * x->N, ty = 2L * y->K * y->N;
    return (tx > ty) - (tx < ty);
}

static long tot(int idx) { return 2L * cand[idx].K * cand[idx].N; }

static void setup(int idx) {
    K = cand[idx].K;
    setup_group(cand[idx].m, cand[idx].k2, cand[idx].r);
}

/* ------------------------------------------------------------ output */

static void restore_best(void) {
    memcpy(sig, bestSig, sizeof sig);
    memcpy(gv, bestGv, sizeof gv);
    for (int t = 0; t < d; t++)
        for (int i = 0; i < K; i++) {
            isig[t][sig[t][i]] = i;
            set_volt(t, i);
        }
}

static void print_result(void) {
    int KN = K * GN, n = 2 * KN;
    int *buf = malloc(sizeof(int) * 2 * (size_t)KN * (size_t)d);
    if (!buf) { printf("0 0\n"); return; }
    long E = 0;
    for (int i = 0; i < K; i++)
        for (int x = 0; x < GN; x++) {
            int v = i * GN + x;
            int tg[MAXD];
            int c = 0;
            for (int t = 0; t < d; t++)
                tg[c++] = KN + sig[t][i] * GN + mulR[t][i][x];
            for (int p = 1; p < c; p++) {
                int z = tg[p], q = p - 1;
                while (q >= 0 && tg[q] > z) { tg[q + 1] = tg[q]; q--; }
                tg[q + 1] = z;
            }
            for (int p = 0; p < c; p++)
                if (p == 0 || tg[p] != tg[p - 1]) {
                    buf[2 * E] = v;
                    buf[2 * E + 1] = tg[p];
                    E++;
                }
        }
    printf("%d %ld\n", n, E);
    for (long e = 0; e < E; e++) printf("%d %d\n", buf[2 * e], buf[2 * e + 1]);
    free(buf);
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

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > 2L * MAXK * MAXN) hi = 2L * MAXK * MAXN;
    if (lo < 2) lo = 2;

    gen_cands(lo, hi);
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best = -1;
    long bestT = 0;

    /* Phase 1: binary search over the sorted candidates. Feasibility is roughly
     * monotone in the total order. Each probe gets a fraction of the remaining time. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        double rem = t_end - now();
        double slice = rem * 0.2;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup(mid);
        if (anneal(now() + slice)) {
            if (tot(mid) > bestT) {
                bestT = tot(mid);
                best = mid;
                memcpy(bestSig, sig, sizeof sig);
                memcpy(bestGv, gv, sizeof gv);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: leftover time on candidates with a strictly larger total. */
    int fails = 0;
    int idx = (best < 0) ? 0 : best + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (tot(idx) <= bestT) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup(idx);
        if (anneal(now() + slice)) {
            bestT = tot(idx);
            best = idx;
            memcpy(bestSig, sig, sizeof sig);
            memcpy(bestGv, gv, sizeof gv);
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (best < 0) {
        printf("0 0\n");
        return 0;
    }
    setup(best);
    restore_best();
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

    # Multi-fibre voltage lifts over semidirect groups, searched inside a window
    # below the Moore bound.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 6)
        hi = mb // 3
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
