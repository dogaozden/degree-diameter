"""Multi-base affine voltage lifts for the bipartite degree-diameter problem.

Change from the parent: the parent searched only Haar graphs, which are lifts with one
base vertex per side. This version searches general bipartite voltage graphs. The base
graph has K vertices per side (K = 1..4). It is d-regular, given by d permutations
sigma_t of {0..K-1} with a voltage s_t in a group G = Z_m x| Z_g2 (r^g2 = 1 mod m).
The lift has 2*K*|G| vertices. Left multiplication by G preserves all edges and acts
transitively on each fibre, so the diameter check needs only 2K BFS runs, one from each
fibre representative. Simulated annealing moves voltages and permutations. Candidates are
tried in ascending vertex count above the current best, so each success raises the bar.

Safety: Python keeps the projective-plane, Araujo-Lopez and generalized-quadrangle
graphs and the K_{d,d} fallback. Every C result is checked with lib.is_valid before use.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over Z_m x|_r Z_g2.
 * Usage: prog d D seed time_limit lo hi     (lo, hi = vertex-count range; stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 4
#define MAXN 4096
#define MAXV (2 * MAXK * MAXN)

typedef struct { int m, g2, r, k, N, V; unsigned key; } Cand;

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

/* ---------------------------------------------------------- group Z_M x| Z_G2
 * Element (a,b) is coded a*G2 + b. Product: (a,b)(c,e) = (a + r^b c, b + e).
 * Requires r^G2 = 1 mod M, which makes the product associative. */
static int M_, G2_, R_, NG;
static int PW[MAXN];

static void setup_group(int m, int g2, int r, int N) {
    M_ = m; G2_ = g2; R_ = r; NG = N;
    PW[0] = 1 % m;
    for (int b = 1; b < g2; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / G2_, b = x - a * G2_;
    int c = y / G2_, e = y - c * G2_;
    int na = (a + PW[b] * c) % M_;
    int nb = (b + e) % G2_;
    return na * G2_ + nb;
}

static inline int ginv(int x) {
    int a = x / G2_, b = x - a * G2_;
    int nb = (G2_ - b) % G2_;
    int na = (M_ - (PW[nb] * a) % M_) % M_;
    return na * G2_ + nb;
}

/* ---------------------------------------------------------- lift state
 * A vertex (i,g) = i*NG + g, B vertex (j,h) = K*NG + j*NG + h.
 * Dart t: A(i,g) ~ B(SIG[t][i], g * VS[t]) for all g. Each vertex then has degree d.
 * FW[t][g] = g*s_t; BW[t][h] = h*s_t^-1. */
static int K;
static int SIG[MAXD][MAXK], SINV[MAXD][MAXK];
static int VS[MAXD];
static int FW[MAXD][MAXN], BW[MAXD][MAXN];
static int VIS[MAXV], QUE[MAXV];
static int stamp_ = 0;

static void set_perm_inv(int t) {
    for (int i = 0; i < K; i++) SINV[t][SIG[t][i]] = i;
}

static void set_volt(int t, int s) {
    VS[t] = s;
    int si = ginv(s);
    for (int g = 0; g < NG; g++) {
        FW[t][g] = gmul(g, s);
        BW[t][g] = gmul(g, si);
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = NG, KN = K * N;
    stamp_++;
    int head = 0, tail = 0;
    QUE[tail++] = src;
    VIS[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = QUE[head++];
            if (v < KN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int w = KN + SIG[t][i] * N + FW[t][g];
                    if (VIS[w] != stamp_) { VIS[w] = stamp_; QUE[tail++] = w; }
                }
            } else {
                int u = v - KN;
                int j = u / N, h = u - j * N;
                for (int t = 0; t < d; t++) {
                    int w = SINV[t][j] * N + BW[t][h];
                    if (VIS[w] != stamp_) { VIS[w] = stamp_; QUE[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Cost 0 iff the lift is simple (no duplicate darts) and has diameter <= D.
 * Vertex transitivity within each fibre means one BFS per fibre suffices. */
static long eval_cost(void) {
    int V = 2 * K * NG, KN = K * NG;
    long cov = 0;
    for (int i = 0; i < K; i++) cov += V - bfs_count(i * NG);
    for (int j = 0; j < K; j++) cov += V - bfs_count(KN + j * NG);
    long dup = 0;
    for (int t = 0; t < d; t++)
        for (int u = t + 1; u < d; u++)
            if (VS[t] == VS[u])
                for (int i = 0; i < K; i++)
                    if (SIG[t][i] == SIG[u][i]) dup++;
    return cov + 8 * dup;
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) SIG[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = SIG[t][i]; SIG[t][i] = SIG[t][j]; SIG[t][j] = tmp;
        }
        set_perm_inv(t);
        set_volt(t, rndint(NG));
    }
}

/* Simulated annealing on the current group and K. Returns 1 on cost 0, 0 on timeout. */
static int anneal(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_state();
        long cost = eval_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d);
            if (K > 1 && rndint(2) == 0) {
                int a = rndint(K), b = rndint(K - 1);
                if (b >= a) b++;
                int tmp = SIG[t][a]; SIG[t][a] = SIG[t][b]; SIG[t][b] = tmp;
                set_perm_inv(t);
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = SIG[t][a]; SIG[t][a] = SIG[t][b]; SIG[t][b] = tmp;
                    set_perm_inv(t);
                }
            } else {
                int old = VS[t];
                set_volt(t, rndint(NG));
                long c2 = eval_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    set_volt(t, old);
                }
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ---------------------------------------------------------- candidates */

static Cand *cands = NULL;
static int ncand = 0, capc = 0;

static void push_cand(int m, int g2, int r, int k, int N) {
    if (ncand == capc) {
        int nc2 = capc ? 2 * capc : 4096;
        Cand *tmp = realloc(cands, sizeof(Cand) * (size_t)nc2);
        if (!tmp) { printf("0 0\n"); exit(0); }
        cands = tmp;
        capc = nc2;
    }
    Cand c;
    c.m = m; c.g2 = g2; c.r = r; c.k = k; c.N = N; c.V = 2 * k * N; c.key = 0;
    cands[ncand++] = c;
}

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
    return 0;
}

/* ---------------------------------------------------------- main */

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

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 4) lo = 4;

    /* N ranges for each base size K = k, where the vertex count is 2*k*N. */
    int nlo[MAXK + 1], nhi[MAXK + 1];
    int nmin = MAXN + 1, nmax = 0;
    for (int k = 1; k <= MAXK; k++) {
        long a = (lo + 2L * k - 1) / (2L * k);
        long b = hi / (2L * k);
        if (a < 2) a = 2;
        if (b > MAXN) b = MAXN;
        nlo[k] = (int)a;
        nhi[k] = (int)b;
        if (a <= b) {
            if (a < nmin) nmin = (int)a;
            if (b > nmax) nmax = (int)b;
        }
    }
    for (int N = nmin; N <= nmax; N++) {
        for (int m = 2; m <= N; m++) {
            if (N % m) continue;
            int g2 = N / m;
            for (int r = 1; r < m; r++) {
                if (gcd_l(r, m) != 1) continue;
                if (powmod_l(r, g2, m) != 1) continue;
                for (int k = 1; k <= MAXK; k++)
                    if (N >= nlo[k] && N <= nhi[k]) push_cand(m, g2, r, k, N);
            }
        }
    }
    if (ncand == 0) {
        printf("0 0\n");
        return 0;
    }
    for (int i = 0; i < ncand; i++) cands[i].key = (unsigned)rnd();
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    int have = 0, bestV = 0;
    Cand bestC;
    static int bSIG[MAXD][MAXK];
    static int bVS[MAXD];

    /* Ascending passes. Each success raises the bar. Failed candidates are retried
     * with fresh random starts in later passes while time remains. */
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < ncand; ci++) {
            if (cands[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            setup_group(cands[ci].m, cands[ci].g2, cands[ci].r, cands[ci].N);
            K = cands[ci].k;
            if (anneal(now() + slice)) {
                have = 1;
                bestV = cands[ci].V;
                bestC = cands[ci];
                memcpy(bSIG, SIG, sizeof SIG);
                memcpy(bVS, VS, sizeof VS);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bestC.m, bestC.g2, bestC.r, bestC.N);
    K = bestC.k;
    memcpy(SIG, bSIG, sizeof SIG);
    for (int t = 0; t < d; t++) {
        set_perm_inv(t);
        set_volt(t, bVS[t]);
    }
    int KN = K * NG;
    printf("%d %d\n", 2 * KN, KN * d);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < NG; g++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * NG + g, KN + SIG[t][i] * NG + FW[t][g]);
    free(cands);
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

    # Search: multi-base voltage lifts over Z_m x| Z_g2, aimed above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
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
