"""Two-orbit-per-side affine voltage lifts for the bipartite degree-diameter problem.

New in this version: the parent searched only Haar graphs (one orbit per side). Here the
C engine also searches a 4-orbit family. Take the affine group G = F_q x| H (order N) and
put two orbits on each side: L_0, L_1, R_0, R_1, each a copy of G. Each left orbit gets d
darts. For a split a in [1, d-1], darts from L_0 go a to R_0 and d-a to R_1, and darts from
L_1 go d-a to R_0 and a to R_1. Each dart carries a group element s, and L_{i,x} ~ R_{j,xs}.
Within one (i, j) block the s values must be distinct, so the graph is simple. Every
vertex has degree d and the graph is bipartite with 4N vertices.

Left multiplication by G acts transitively on each of the four orbits, so diameter <= D
reduces to four BFS runs, one from each orbit representative. The search is simulated
annealing over the dart elements and the split a. Phase 1 binary-searches the group order
N, which gives 4N vertices. The Python driver runs this family first, then the parent's
Haar (one orbit per side) search, and keeps the largest graph that passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi P     (stdin ignored)
 *   P = 1: Haar graph (2N vertices), P = 2: two orbits per side (4N vertices).
 *   lo, hi bound the group order N = q*c.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
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
#define MAXN 4096
#define MAXD 32
#define MAXNT 64
#define MAXCAND 16384

typedef struct { int q, p, k, c, N; } Cand;

static int d, D;
static int PP = 1;      /* orbits per side */
static int NT = 0;      /* darts = PP * d */
static int A = 0;       /* split for PP == 2 */
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

/* ------------------------------------------------------------ group F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c). */
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

/* ------------------------------------------------------------ voltage lift state */

static int Sv[MAXNT], bestSv[MAXNT], bestA;
static int fwd[MAXNT][MAXN], bwd[MAXNT][MAXN];
static int li_[MAXNT], rj_[MAXNT];
static int RD[2][MAXD];
static int vis[4 * MAXN], que[4 * MAXN];
static int stamp_ = 0;

/* Left orbit i owns darts i*d .. i*d+d-1. For P = 2 the dart blocks are
 * L0->R0: a, L0->R1: d-a, L1->R0: d-a, L1->R1: a. Each right orbit gets d darts. */
static void set_split(int P, int a) {
    PP = P;
    A = a;
    NT = P * d;
    for (int t = 0; t < NT; t++) {
        int i = t / d, k = t - i * d;
        li_[t] = i;
        if (P == 1) rj_[t] = 0;
        else if (i == 0) rj_[t] = (k < a) ? 0 : 1;
        else rj_[t] = (k < d - a) ? 0 : 1;
    }
    int cnt[2] = {0, 0};
    for (int t = 0; t < NT; t++) {
        int j = rj_[t];
        RD[j][cnt[j]++] = t;
    }
}

/* Dart t has group element x. Left L_{i,g} ~ R_{j, g*x}. */
static void set_dart(int t, int x) {
    Sv[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[t][g] = gmul(g, x);
        bwd[t][g] = gmul(g, xi);
    }
}

/* Two darts in the same (left, right) block must have distinct elements (simple graph). */
static int conflict(int t, int x) {
    for (int u = 0; u < NT; u++)
        if (u != t && li_[u] == li_[t] && rj_[u] == rj_[t] && Sv[u] == x) return 1;
    return 0;
}

/* Vertices: L_{i,g} = i*N + g, R_{j,h} = PP*N + j*N + h. */
static int bfs_reach(int src) {
    int N = GN, base = PP * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < d; k++) {
                    int t = i * d + k;
                    int u = base + rj_[t] * N + fwd[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - base;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < d; k++) {
                    int t = RD[j][k];
                    int u = li_[t] * N + bwd[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbit representatives: one BFS per orbit, using vertex transitivity within each orbit. */
static long cost_all(void) {
    int N = GN, V = 2 * PP * N;
    long c = 0;
    for (int o = 0; o < 2 * PP; o++)
        c += V - bfs_reach(o * N);
    return c;
}

/* Simulated annealing over dart elements and split. Returns 1 at cost 0 (state kept). */
static int search_state(double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        int a = (PP == 2) ? 1 + rndint(d - 1) : 0;
        set_split(PP, a);
        for (int t = 0; t < NT; t++) Sv[t] = -1;
        for (int t = 0; t < NT; t++) {
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (conflict(t, x) && tries < 100000);
            Sv[t] = x;
        }
        for (int t = 0; t < NT; t++) set_dart(t, Sv[t]);
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(NT);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (conflict(t, x) && tries < 100000);
            int old = Sv[t];
            set_dart(t, x);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_state(void) {
    int N = GN;
    printf("%d %d\n", 2 * PP * N, NT * N);
    for (int t = 0; t < NT; t++) {
        int i = li_[t], j = rj_[t];
        for (int x = 0; x < N; x++)
            printf("%d %d\n", i * N + x, PP * N + j * N + fwd[t][x]);
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
    int P = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || (P != 1 && P != 2)) {
        printf("0 0\n");
        return 0;
    }
    PP = P;
    if (hi > MAXN) hi = MAXN;
    if (lo < d + 1) lo = d + 1;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
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

    /* Phase 1: binary search over group orders; each probe gets an equal share
     * of the remaining time over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_state(now() + slice)) {
            if (cand[mid].N > bestN) {
                bestN = cand[mid].N;
                best_idx = mid;
                memcpy(bestSv, Sv, sizeof(int) * (size_t)NT);
                bestA = A;
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].N <= bestN) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_state(now() + slice)) {
            bestN = cand[idx].N;
            best_idx = idx;
            memcpy(bestSv, Sv, sizeof(int) * (size_t)NT);
            bestA = A;
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
    set_split(PP, bestA);
    for (int t = 0; t < NT; t++) set_dart(t, bestSv[t]);
    print_state();
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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        def left():
            return 0.85 * time_limit - (time.monotonic() - t0) - 2.0

        # Stage A (new): two orbits per side, 4N vertices. Needs 4N > current best.
        lo4 = max(best[0] // 4 + 1, mb // 16, d + 1)
        hi4 = mb // 4
        b4 = 0.6 * left()
        if b4 > 3.0 and lo4 <= hi4:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(b4, 2), lo4, hi4, 2],
                                 stdin_graph=None, timeout=b4 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

        # Stage B: one orbit per side (Haar graph, 2N vertices) with the remaining time.
        lo2 = max(best[0] // 2 + 1, mb // 8, d + 1)
        hi2 = mb // 2
        b2 = left()
        if b2 > 3.0 and lo2 <= hi2:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(b2, 2), lo2, hi2, 1],
                                 stdin_graph=None, timeout=b2 + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
