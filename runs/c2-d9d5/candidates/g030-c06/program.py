"""Voltage lifts of small bipartite multigraph bases over semidirect groups.

Different family from the parent's single-orbit Haar graphs. A base has B left and B right
vertices. Each of the d darts t is a perfect matching layer: left i joins right sg_t(i), and the
lifted edge joins (a_i, g) to (b_{sg_t(i)}, g * v_t) for g in G = Z_m x| Z_k. Left multiplication
by G is an automorphism group acting regularly on each fibre, so the diameter check needs only
2B BFS runs, one from each fibre's identity vertex. Multi-edges created by coincident darts are
removed at output, which keeps degree <= d and does not change any distance.

Search: iterated annealing over the darts (voltage change or permutation swap), with the
incumbent perturbed between rounds. Candidates are tried in ascending order of vertex count,
starting just above the Moore-quarter level, so the largest success is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Semidirect-lift search. Usage: prog d D seed time_limit lo hi   (stdin ignored)
 * Output: "n m" then m lines "u v", or "0 0". Vertices: left i*N+g, right B*N+j*N+h.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXB 4
#define MAXD 16
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 300000

typedef struct { int B, m, k, r, V; } Cand;

typedef struct {
    int sg[MAXB];  /* left i -> right sg[i]; a permutation of 0..B-1 */
    int si[MAXB];  /* inverse permutation */
    int v;         /* voltage in G */
    int vi;        /* inverse voltage */
} Dart;

static int d, D, B, N;
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

/* ------------------------------------------------------------ group Z_m x| Z_k */

static int MULT[MAXN][MAXN];
static int INV[MAXN];
static int rpow[MAXN];

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod_i(int a, int e, int m) {
    long long r = 1 % m, x = a % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c, b + e). Needs r^k = 1 mod m. */
static void setup_group(int m, int k, int r) {
    N = m * k;
    rpow[0] = 1 % m;
    for (int b = 1; b < k; b++) rpow[b] = (rpow[b - 1] * r) % m;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int na = (a + rpow[b] * c) % m;
            MULT[x][y] = na * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        int bi = (k - b) % k;
        int ai = (m - (rpow[bi] * a) % m) % m;
        INV[x] = ai * k + bi;
    }
}

/* ------------------------------------------------------------ darts */

static Dart dart[MAXD];
static Dart incD[MAXD];

static void derive(Dart *x) {
    for (int i = 0; i < B; i++) x->si[x->sg[i]] = i;
    x->vi = INV[x->v];
}

static void random_dart(Dart *x) {
    for (int i = 0; i < B; i++) x->sg[i] = i;
    for (int i = B - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x->sg[i];
        x->sg[i] = x->sg[j];
        x->sg[j] = t;
    }
    x->v = rndint(N);
    derive(x);
}

static void mutate(Dart *x) {
    if (B > 1 && rndint(2) == 0) {
        int i1 = rndint(B), i2 = rndint(B - 1);
        if (i2 >= i1) i2++;
        int t = x->sg[i1];
        x->sg[i1] = x->sg[i2];
        x->sg[i2] = t;
    } else {
        x->v = rndint(N);
    }
    derive(x);
}

/* ------------------------------------------------------------ BFS cost */

static int vst[MAXV];
static int stampc = 0;
static int que[MAXV];

static int ball_count(int src) {
    int BN = B * N;
    stampc++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vst[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + dart[t].sg[i] * N + MULT[g][dart[t].v];
                    if (vst[u] != stampc) { vst[u] = stampc; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, h = w % N;
                for (int t = 0; t < d; t++) {
                    int u = dart[t].si[j] * N + MULT[h][dart[t].vi];
                    if (vst[u] != stampc) { vst[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fibres are regular G-orbits, so one BFS per base vertex (at the identity) decides the diameter. */
static long cover_cost(void) {
    int BN = B * N, V = 2 * BN;
    long c = 0;
    for (int i = 0; i < B; i++) c += V - ball_count(i * N);
    for (int j = 0; j < B; j++) c += V - ball_count(BN + j * N);
    return c;
}

/* Iterated annealing: random start first, then the incumbent with two moves applied. */
static int search_cfg(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            for (int t = 0; t < d; t++) random_dart(&dart[t]);
        } else {
            memcpy(dart, incD, sizeof(Dart) * (size_t)d);
            for (int s = 0; s < 2; s++) mutate(&dart[rndint(d)]);
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d);
            Dart old = dart[t];
            mutate(&dart[t]);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                dart[t] = old;
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incD, dart, sizeof(Dart) * (size_t)d);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static int left_nbrs(int u, int *tgt) {
    int BN = B * N;
    int i = u / N, g = u % N;
    int cnt = 0;
    for (int t = 0; t < d; t++) {
        int w = BN + dart[t].sg[i] * N + MULT[g][dart[t].v];
        int dup = 0;
        for (int s = 0; s < cnt; s++)
            if (tgt[s] == w) { dup = 1; break; }
        if (!dup) tgt[cnt++] = w;
    }
    return cnt;
}

static void print_graph(void) {
    int BN = B * N, V = 2 * BN;
    int tgt[MAXD];
    long m = 0;
    for (int u = 0; u < BN; u++) m += left_nbrs(u, tgt);
    printf("%d %ld\n", V, m);
    for (int u = 0; u < BN; u++) {
        int cnt = left_nbrs(u, tgt);
        for (int s = 0; s < cnt; s++) printf("%d %d\n", u, tgt[s]);
    }
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];
static int ncand = 0;

static void add_cand(int b, int m, int k, int r) {
    if (ncand >= MAXCAND) return;
    Cand c;
    c.B = b; c.m = m; c.k = k; c.r = r; c.V = 2 * b * m * k;
    cand[ncand++] = c;
}

static int cmp_V(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->V > y->V) - (x->V < y->V);
}

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

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2 * d) lo = 2 * d;

    for (int b = 1; b <= MAXB; b++) {
        int nlo = (lo + 2 * b - 1) / (2 * b);
        if (nlo < 1) nlo = 1;
        int nhi = hi / (2 * b);
        if (nhi > MAXN) nhi = MAXN;
        for (int Nn = nlo; Nn <= nhi; Nn++) {
            for (int m = 1; m <= Nn; m++) {
                if (Nn % m) continue;
                int k = Nn / m;
                if (m == 1) {
                    add_cand(b, 1, k, 0);
                    continue;
                }
                for (int r = 1; r < m; r++) {
                    if (gcd_i(r, m) != 1) continue;
                    if (powmod_i(r, k, m) != 1) continue;
                    add_cand(b, m, k, r);
                }
            }
        }
    }
    if (ncand == 0) {
        printf("0 0\n");
        return 0;
    }
    /* Shuffle, then stable-ish sort by vertex count: ascending, random within a count. */
    for (int i = ncand - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand t = cand[i];
        cand[i] = cand[j];
        cand[j] = t;
    }
    qsort(cand, (size_t)ncand, sizeof(Cand), cmp_V);

    int bestV = 0, bB = 0, bm = 0, bk = 0, br = 0;
    static Dart bestD[MAXD];
    for (int ci = 0; ci < ncand; ci++) {
        double rem = t_end - now();
        if (rem < 0.5) break;
        Cand c = cand[ci];
        if (c.V <= bestV) continue;
        double slice = 0.1 * rem;
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        setup_group(c.m, c.k, c.r);
        B = c.B;
        if (search_cfg(now() + slice)) {
            bestV = 2 * B * N;
            bB = B; bm = c.m; bk = c.k; br = c.r;
            memcpy(bestD, dart, sizeof(Dart) * (size_t)d);
        }
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bm, bk, br);
    B = bB;
    memcpy(dart, bestD, sizeof(Dart) * (size_t)d);
    print_graph();
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
        # Exact Moore graph for D = 3 when d - 1 is a prime power.
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

    # Search: semidirect-group voltage lifts with 1..4 base vertices per side.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 4)
        hi = mb // 2
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
