"""Affine-group lifts with one or two vertices per side, for the bipartite degree-diameter problem.

New construction in this version: a 2x2 base lift over the affine group G = F_q x| H.
The parent searched only Haar graphs (one vertex per side, 2N vertices). Here the
graph has four blocks L1, L2, R1, R2, each a copy of G, so it has 4N vertices.
Darts (a, b, s) join L_a(g) to R_b(g s). Each left block has d darts, and each right
block has d darts. Two classes (a=0,b=0) and (a=1,b=1) have size x, and the other
two have size d-x, with 1 <= x <= d-1. Within a class the elements s are distinct,
so the graph is simple, bipartite and d-regular. Left multiplication by G preserves
every block, so the diameter check needs only four BFS runs, from the identity of
each block. The C engine searches x, the darts and the group order N, with simulated
annealing on the total number of uncovered (source, vertex) pairs.

Budget: the 2x2 lift gets 55% of the time. The Haar lift (one block per side) gets
the rest and is kept as a fallback, so the parent's best result is not lost. Each
probe in the binary search over group orders gets an equal share of its remaining
time.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Affine-group lift search with 1 or 2 vertices per side.
 * Usage: prog d D seed time_limit lo hi nside
 *   lo, hi : range of the group order N.
 *   nside=1: Haar graph on 2N vertices, d darts L_g ~ R_{g s}.
 *   nside=2: 2x2 base lift on 4N vertices. Blocks L1, L2, R1, R2 of size N.
 *            Darts (a,b,s) join L_a(g) to R_b(g s). Classes (0,0),(1,1) have size x,
 *            classes (0,1),(1,0) have size d-x, and 1 <= x <= d-1.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXDARTS 64
#define MAXV (4 * MAXN)
#define MAXCAND 8192

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, nside, nblk;
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

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

static int ndart;
static int dcl_a[MAXDARTS], dcl_b[MAXDARTS];   /* dart j joins L_a to R_b */
static int dS[MAXDARTS], dSi[MAXDARTS];
static int fwd[MAXDARTS][MAXN], bwd[MAXDARTS][MAXN];
static int nbd[4][MAXD];                       /* darts incident to each block */
static int bestS[MAXDARTS];
static int bestX = 0, curX = 0;
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Left blocks are 0..nside-1, right blocks are nside..2*nside-1.
 * Vertex id = block * GN + index. */
static void layout(int x) {
    if (nside == 1) {
        ndart = d;
        for (int i = 0; i < d; i++) { dcl_a[i] = 0; dcl_b[i] = 0; }
    } else {
        ndart = 2 * d;
        for (int i = 0; i < d; i++) {
            dcl_a[i] = 0;
            dcl_b[i] = (i < x) ? 0 : 1;
        }
        for (int i = 0; i < d; i++) {
            dcl_a[d + i] = 1;
            dcl_b[d + i] = (i < d - x) ? 0 : 1;
        }
    }
    for (int blk = 0; blk < nblk; blk++) {
        int cnt = 0;
        for (int j = 0; j < ndart; j++) {
            int inb = (blk < nside) ? (dcl_a[j] == blk) : (dcl_b[j] == blk - nside);
            if (inb && cnt < MAXD) nbd[blk][cnt++] = j;
        }
    }
}

static void set_dart(int i, int s) {
    dS[i] = s;
    dSi[i] = ginv(s);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, s);
        bwd[i][g] = gmul(g, dSi[i]);
    }
}

/* True if element s would repeat inside the class of dart i, among darts j < upto, j != i. */
static int conflict_upto(int i, int s, int upto) {
    for (int j = 0; j < upto; j++) {
        if (j == i) continue;
        if (dcl_a[j] == dcl_a[i] && dcl_b[j] == dcl_b[i] && dS[j] == s) return 1;
    }
    return 0;
}

/* Number of vertices reached from src within distance D. */
static int bfs_reach(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int k = v / GN, idx = v - k * GN;
            const int *nb = nbd[k];
            if (k < nside) {
                for (int t = 0; t < d; t++) {
                    int j = nb[t];
                    int u = (nside + dcl_b[j]) * GN + fwd[j][idx];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                for (int t = 0; t < d; t++) {
                    int j = nb[t];
                    int u = dcl_a[j] * GN + bwd[j][idx];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* The group acts by left multiplication and preserves every block, so one BFS
 * from the identity of each block decides the diameter. */
static long cover_cost(void) {
    long c = 0;
    int V = nblk * GN;
    for (int s = 0; s < nblk; s++)
        c += (long)(V - bfs_reach(s * GN));
    return c;
}

/* Simulated annealing over the darts, restarted with a fresh x each time.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 4000;
    while (now() < until) {
        int x = d / 2;
        if (nside == 2) x = 1 + rndint(d - 1);
        curX = x;
        layout(x);
        for (int i = 0; i < ndart; i++) {
            int s;
            do { s = rndint(N); } while (conflict_upto(i, s, i));
            set_dart(i, s);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(ndart);
            int old = dS[i];
            int s;
            do { s = rndint(N); } while (conflict_upto(i, s, ndart));
            set_dart(i, s);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    long m = (long)ndart * N;
    printf("%d %ld\n", nblk * N, m);
    for (int j = 0; j < ndart; j++) {
        int a = dcl_a[j], b = nside + dcl_b[j];
        for (int g = 0; g < N; g++)
            printf("%d %d\n", a * N + g, b * N + fwd[j][g]);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    nside = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (nside != 1 && nside != 2)) {
        printf("0 0\n");
        return 0;
    }
    nblk = 2 * nside;
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int best_idx = -1, bestN = 0;

    /* Phase 1: binary search for the largest feasible group order. Each probe
     * gets an equal share of the remaining time. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                bestX = curX;
                memcpy(bestS, dS, sizeof(int) * (size_t)ndart);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend the leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            bestX = curX;
            memcpy(bestS, dS, sizeof(int) * (size_t)ndart);
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
    setup_group(cand[best_idx].q, cand[best_idx].p, cand[best_idx].k, cand[best_idx].c);
    layout(bestX);
    for (int i = 0; i < ndart; i++) set_dart(i, bestS[i]);
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


def _run_lift(d, D, seed, budget, lo, hi, nside):
    """Run the C lift search with the N-range [lo, hi] and return (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, nside],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage A: 2x2 base lift on 4N vertices, with N = group order.
        total = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        budget_a = 0.55 * total
        lo_a = max(best[0] // 4 + 1, mb // 16)
        hi_a = mb // 4
        if budget_a > 2.0 and lo_a <= hi_a:
            try:
                consider(_run_lift(d, D, seed, budget_a, lo_a, hi_a, 2))
            except Exception:
                pass

        # Stage B: Haar lift on 2N vertices, with the remaining budget.
        total_b = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo_b = max(best[0] // 2 + 1, mb // 8)
        hi_b = mb // 2
        if total_b > 2.0 and lo_b <= hi_b:
            try:
                consider(_run_lift(d, D, seed + 1, total_b, lo_b, hi_b, 1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
