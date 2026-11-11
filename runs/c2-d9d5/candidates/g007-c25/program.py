"""Multi-vertex voltage lifts over semidirect groups for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs (base = two vertices with
d parallel darts) over affine groups F_q x| H. This version searches a different family:
base graphs with a A-vertices and a B-vertices (a = 1..4). The base is the union of d
permutation matrices, so the base is d-regular and bipartite. Each dart carries a voltage
in a semidirect product Z_m x| Z_k (r^k = 1 mod m). The lift has 2*a*N vertices, is
d-regular and bipartite, and is simple when the darts sharing a base pair have distinct
voltages. Left translations act on each fibre, so diameter <= D is checked by BFS from
the 2a fibre representatives. Simulated annealing moves voltages and permutations.
Candidates are tried in ascending order of order, with random group choices and restarts.

Risk: the parent's affine Haar family reached 2510 on d=9, D=5. This engine must beat
that from a different family, so it may not. The Python fallback (Haar K_{d,d}, projective
plane, Araujo-Pardo-Lopez, GQ) keeps every returned graph valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage lifts over Z_m x| Z_k.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*a*N.
 * Output: "n m" then m lines "u v" for the first valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define NMAX 2400
#define AMAX 4
#define MAXD 32
#define VMAX (2 * AMAX * NMAX)
#define MAXCAND 16384
#define MAXOPT 256
#define MAXEDGE 400000

typedef struct { int V, a, N; } Cand;

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

/* ------------------------------------------------------------ group tables */

static short mt[NMAX * NMAX];
static int inv_[NMAX];
static int pwr[NMAX];
static int A_ = 1, N_ = 1;

static int opt_m[MAXOPT], opt_k[MAXOPT], opt_r[MAXOPT], nopt = 0;

static long gcd_l(long x, long y) {
    while (y) { long t = x % y; x = y; y = t; }
    return x;
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

/* Semidirect products Z_m x| Z_k with r^k = 1 mod m and gcd(r, m) = 1. */
static void list_groups(int N) {
    nopt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_l(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (nopt < MAXOPT) {
                opt_m[nopt] = m;
                opt_k[nopt] = k;
                opt_r[nopt] = r;
                nopt++;
            }
        }
    }
}

/* Element (a, b) is coded as a*k + b. Product: (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). */
static void setup_group(int N, int m, int k, int r) {
    pwr[0] = 1 % m;
    for (int b = 1; b < k; b++) pwr[b] = (int)((long)pwr[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            int a = (int)((a1 + (long)pwr[b1] * a2) % m);
            int b = (b1 + b2) % k;
            mt[x * N + y] = (short)(a * k + b);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x * N + y] == 0) { inv_[x] = y; break; }
}

/* ------------------------------------------------------------ lift state */

/* Base: A_i (i < a) and B_j (j < a). Dart (t, i) joins A_i to B_{perm[t][i]} with voltage volt[t][i].
 * Lift: A_i,g ~ B_j,g*s for each dart. Each A and B vertex has exactly d darts. */
static int perm[MAXD][AMAX], volt[MAXD][AMAX], pinv[MAXD][AMAX];
static int fa_j[AMAX][MAXD], fa_s[AMAX][MAXD];
static int fb_i[AMAX][MAXD], fb_s[AMAX][MAXD];
static int vis[VMAX], que[VMAX];
static int stamp_ = 0;

static int nE = 0, bestA = 0, bestN = 0, bestV = 0;
static int EU[MAXEDGE], EV[MAXEDGE];

static void rebuild_adj(void) {
    int a = A_;
    for (int t = 0; t < d; t++)
        for (int i = 0; i < a; i++) pinv[t][perm[t][i]] = i;
    for (int i = 0; i < a; i++)
        for (int t = 0; t < d; t++) {
            fa_j[i][t] = perm[t][i];
            fa_s[i][t] = volt[t][i];
        }
    for (int j = 0; j < a; j++)
        for (int t = 0; t < d; t++) {
            int i = pinv[t][j];
            fb_i[j][t] = i;
            fb_s[j][t] = inv_[volt[t][i]];
        }
}

static int count_dups(void) {
    int dup = 0;
    for (int i = 0; i < A_; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = t + 1; t2 < d; t2++)
                if (perm[t][i] == perm[t2][i] && volt[t][i] == volt[t2][i]) dup++;
    return dup;
}

/* Number of vertices within distance D of src. */
static int bfs_cover(int src) {
    int a = A_, N = N_;
    int aN = a * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < aN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int j = fa_j[i][t];
                    int u = (a + j) * N + mt[g * N + fa_s[i][t]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int idx = v - aN;
                int j = idx / N, h = idx % N;
                for (int t = 0; t < d; t++) {
                    int i = fb_i[j][t];
                    int u = i * N + mt[h * N + fb_s[j][t]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Uncovered (rep, vertex) pairs over the 2a fibre representatives, plus a penalty for duplicate darts. */
static long cost_full(void) {
    int a = A_, N = N_;
    long V = 2L * a * N;
    long c = 0;
    for (int i = 0; i < a; i++) c += V - bfs_cover(i * N);
    for (int j = 0; j < a; j++) c += V - bfs_cover((a + j) * N);
    c += 1000L * count_dups();
    return c;
}

static void random_state(void) {
    int a = A_, N = N_;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < a; i++) perm[t][i] = i;
        for (int i = a - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][j];
            perm[t][j] = tmp;
        }
        for (int i = 0; i < a; i++) volt[t][i] = rndint(N);
    }
}

/* Simulated annealing over darts. Returns 1 when a zero-cost lift is found, 0 on timeout. */
static int search(double until) {
    int a = A_, N = N_;
    const int iters = 5000;
    while (now() < until) {
        random_state();
        rebuild_adj();
        long cost = cost_full();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d), i = rndint(a);
            if (a >= 2 && rnd01() < 0.4) {
                int i2 = rndint(a - 1);
                if (i2 >= i) i2++;
                int tmp = perm[t][i];
                perm[t][i] = perm[t][i2];
                perm[t][i2] = tmp;
                rebuild_adj();
                long c2 = cost_full();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = perm[t][i];
                    perm[t][i] = perm[t][i2];
                    perm[t][i2] = tmp;
                    rebuild_adj();
                }
            } else {
                int old = volt[t][i];
                int nv = rndint(N);
                if (nv == old) continue;
                volt[t][i] = nv;
                rebuild_adj();
                long c2 = cost_full();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    volt[t][i] = old;
                    rebuild_adj();
                }
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static void capture(void) {
    int a = A_, N = N_;
    nE = 0;
    for (int i = 0; i < a; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++) {
                int j = fa_j[i][t];
                EU[nE] = i * N + g;
                EV[nE] = (a + j) * N + mt[g * N + fa_s[i][t]];
                nE++;
            }
    bestA = a;
    bestN = N;
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = (const Cand *)x;
    const Cand *q = (const Cand *)y;
    if (p->V != q->V) return p->V < q->V ? -1 : 1;
    if (p->a != q->a) return p->a < q->a ? -1 : 1;
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

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2) lo = 2;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int a = 1; a <= AMAX; a++) {
        long Nlo = (lo + 2L * a - 1) / (2L * a);
        long Nhi = hi / (2L * a);
        if (Nlo < d) Nlo = d;
        if (Nhi > NMAX) Nhi = NMAX;
        if (Nhi > MAXEDGE / (a * d)) Nhi = MAXEDGE / (a * d);
        for (long N = Nlo; N <= Nhi && nc < MAXCAND; N++) {
            cand[nc].V = (int)(2L * a * N);
            cand[nc].a = a;
            cand[nc].N = (int)N;
            nc++;
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    bestV = (int)lo - 1;
    int found = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.03 * rem;
            if (slice < 0.3) slice = 0.3;
            if (slice > rem) slice = rem;
            A_ = cand[ci].a;
            N_ = cand[ci].N;
            list_groups(N_);
            int o = rndint(nopt);
            setup_group(N_, opt_m[o], opt_k[o], opt_r[o]);
            if (search(now() + slice)) {
                bestV = cand[ci].V;
                found = 1;
                capture();
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestA * bestN, nE);
    for (int e = 0; e < nE; e++) printf("%d %d\n", EU[e], EV[e]);
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

    # Search: multi-vertex base lifts over semidirect groups, aimed above the current best.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
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
