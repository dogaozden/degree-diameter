"""Two-orbit voltage lifts over affine groups for the bipartite degree-diameter problem.

Change in this version: the parent searched Haar graphs (one left orbit, one right
orbit, d parallel darts). This version uses a 2x2 base multigraph. Left classes L0, L1
and right classes R0, R1 are joined with multiplicities [[x, d-x], [d-x, x]] for a
random x in [1, d-1], and every dart carries a voltage g in G = Z_q x| H, where q is
prime and H has order c with c | q-1. The lift has 4|G| vertices, is d-regular and
bipartite, and is simple because parallel darts in the same class pair get distinct
voltages. Left multiplication is an automorphism, so diameter <= D reduces to four
BFS runs, one from each class representative. Simulated annealing moves single
voltages, and the group order is found by a time-sliced binary search.

Only prime q is used, so field arithmetic is plain modular arithmetic. The Python side
keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every returned
graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit voltage lift search over affine groups Z_q x| H (q prime).
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 * Vertices: L_i,x = i*N + x (i = 0,1), R_j,x = (2+j)*N + x (j = 0,1), N = |G|.
 * Dart k (from L_dfrom[k] to R_dto[k], voltage dg[k]) gives edges (L,x)-(R,x*g).
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 1200
#define MAXC 1200
#define MAXN 4200
#define MAXD 32
#define NDART (2 * MAXD)
#define MAXCAND 20000

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

static int is_prime(int n) {
    if (n < 2) return 0;
    for (int f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

/* ------------------------------------------------------------ group G = Z_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC];
static int hidx[MAXQ];

/* Element (a, h_j) is coded as a*c + j with h_j = g^(j*(q-1)/c).
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static int setup_group(int q, int c) {
    GQ = q;
    GC = c;
    GN = q * c;
    int fac[32], nf = 0, m = q - 1;
    for (int f = 2; f * f <= m; f++)
        if (m % f == 0) {
            fac[nf++] = f;
            while (m % f == 0) m /= f;
        }
    if (m > 1) fac[nf++] = m;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g0, (q - 1) / fac[i], q) == 1) ok = 0;
        if (ok) g = g0;
    }
    if (g < 0) return 0;
    int step = (q - 1) / c;
    for (int h = 0; h < q; h++) hidx[h] = -1;
    for (int j = 0; j < c; j++) {
        Hel[j] = (int)powmod(g, (long)j * step, q);
        hidx[Hel[j]] = j;
    }
    return 1;
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x - a * GC;
    int b = y / GC, t = y - b * GC;
    int na = (a + (Hel[j] * b) % GQ) % GQ;
    int nj = hidx[(Hel[j] * Hel[t]) % GQ];
    return na * GC + nj;
}

static inline int ginv(int x) {
    int a = x / GC, j = x - a * GC;
    int jn = (GC - j) % GC;
    int na = (GQ - (Hel[jn] * a) % GQ) % GQ;
    return na * GC + jn;
}

/* ------------------------------------------------------------ 2x2 base voltage lift */

static int dfrom[NDART], dto[NDART], dg[NDART], pidx[NDART];
static int plo[4], phi[4];
static int ldart[2][MAXD], rdart[2][MAXD];
static int MX;
static int fwdT[NDART][MAXN], bwdT[NDART][MAXN];

/* Pair (0,0) has x darts, (0,1) has d-x, (1,0) has d-x, (1,1) has x. */
static void set_x(int x) {
    int D2 = 2 * d;
    MX = x;
    for (int k = 0; k < D2; k++) {
        int f, t, p;
        if (k < x) { f = 0; t = 0; p = 0; }
        else if (k < d) { f = 0; t = 1; p = 1; }
        else if (k < D2 - x) { f = 1; t = 0; p = 2; }
        else { f = 1; t = 1; p = 3; }
        dfrom[k] = f;
        dto[k] = t;
        pidx[k] = p;
    }
    plo[0] = 0;  phi[0] = x;
    plo[1] = x;  phi[1] = d;
    plo[2] = d;  phi[2] = D2 - x;
    plo[3] = D2 - x; phi[3] = D2;
    for (int t = 0; t < d; t++) {
        ldart[0][t] = t;
        ldart[1][t] = d + t;
    }
    int cnt[2] = {0, 0};
    for (int k = 0; k < D2; k++) {
        int j = dto[k];
        rdart[j][cnt[j]++] = k;
    }
}

static void set_dart(int k, int g) {
    int N = GN;
    int ig = ginv(g);
    dg[k] = g;
    for (int x = 0; x < N; x++) {
        fwdT[k][x] = gmul(x, g);
        bwdT[k][x] = gmul(x, ig);
    }
}

/* True if voltage g is already used by another dart of the same class pair. */
static int g_used_elsewhere(int k, int g) {
    int p = pidx[k];
    for (int k2 = plo[p]; k2 < phi[p]; k2++)
        if (k2 != k && dg[k2] == g) return 1;
    return 0;
}

/* ------------------------------------------------------------ BFS and cost */

static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int cls = v / N;
            int x = v - cls * N;
            if (cls < 2) {
                for (int t = 0; t < d; t++) {
                    int k = ldart[cls][t];
                    int u = (2 + dto[k]) * N + fwdT[k][x];
                    if (vis[u] != stamp_) {
                        vis[u] = stamp_;
                        que[tail++] = u;
                    }
                }
            } else {
                int j = cls - 2;
                for (int t = 0; t < d; t++) {
                    int k = rdart[j][t];
                    int u = dfrom[k] * N + bwdT[k][x];
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

/* Left multiplication is an automorphism, so one BFS per class representative suffices. */
static long cover_cost(void) {
    int N = GN, V = 4 * N;
    long c = 0;
    c += V - bfs_count(0);
    c += V - bfs_count(N);
    c += V - bfs_count(2 * N);
    c += V - bfs_count(3 * N);
    return c;
}

/* Simulated annealing over (x, voltages) in the current group.
 * Returns 1 when cost 0 is reached (state left in globals), 0 on timeout. */
static int search_group(double until) {
    int N = GN, D2 = 2 * d;
    const int iters = 6000;
    while (now() < until) {
        int x = 1 + rndint(d - 1);
        set_x(x);
        for (int k = 0; k < D2; k++) {
            int g, ok;
            do {
                g = rndint(N);
                ok = 1;
                for (int k2 = plo[pidx[k]]; k2 < k; k2++)
                    if (dg[k2] == g) { ok = 0; break; }
            } while (!ok);
            set_dart(k, g);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(D2);
            int g;
            do { g = rndint(N); } while (g_used_elsewhere(k, g));
            int old = dg[k];
            set_dart(k, g);
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

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 4 * N, 2 * d * N);
    for (int k = 0; k < 2 * d; k++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", dfrom[k] * N + x, (2 + dto[k]) * N + fwdT[k][x]);
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];
static int bestG[NDART], bestX;

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
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXN) hi = MAXN;

    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        if (!is_prime(q)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].q = q;
                cand[nc].c = c;
                cand[nc].N = (int)N;
                nc++;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) {
            cand[j + 1] = cand[j];
            j--;
        }
        cand[j + 1] = t;
    }

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search over orders. Each probe gets an equal share of the
     * remaining time divided by the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) {
            span = (span + 1) / 2;
            probes++;
        }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (!setup_group(cand[mid].q, cand[mid].c)) {
            b = mid - 1;
            continue;
        }
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                bestX = MX;
                memcpy(bestG, dg, sizeof(dg));
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) {
            idx++;
            continue;
        }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (!setup_group(cand[idx].q, cand[idx].c)) {
            idx++;
            continue;
        }
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            bestX = MX;
            memcpy(bestG, dg, sizeof(dg));
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[best_idx].q, cand[best_idx].c);
    set_x(bestX);
    for (int k = 0; k < 2 * d; k++) set_dart(k, bestG[k]);
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

    # Two-orbit voltage lifts over affine groups: 4|G| vertices, so |G| <= moore / 4.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 4 + 1, mb // 16, 2 * d)
        hi = mb // 4
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
