"""Multi-orbit affine lifts for the bipartite degree-diameter problem.

New idea: a bipartite graph with two vertex orbits per side. Each side is split into
two copies of the affine group G = F_q x| C_c. The darts between orbits form a 2x2
block pattern with sizes (x, d-x; d-x, x), where 1 <= x <= d-1. Each left orbit and
each right orbit then has degree exactly d. The orbit count O = 1 is the parent's
Haar lift, so this family contains the parent's graphs as a special case.

Since G acts on each orbit by automorphisms, the diameter test needs one BFS from a
representative of each of the 2O orbits. The cost function is the number of
uncovered (vertex, source) pairs, minimised by simulated annealing over the dart
labels. Each restart draws a fresh x.

Candidates from both orbit counts are merged and sorted by vertex count. A binary
search with equal time slices finds the largest feasible count, and phase 2 uses
the leftover time above it. Python keeps the projective-plane, Araujo-Lopez,
W(q) and K_{d,d} baselines. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine lift search.
 * Usage: prog d D seed time_limit vlo vhi     (stdin ignored)
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
#define MAXDD 64
#define MAXV (4 * MAXN)
#define MAXCAND 16384
#define ITERS 4000

typedef struct { int O, q, p, k, c, N, V; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| C_c */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). Identity is 0. */
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

/* ------------------------------------------------------------ multi-orbit layout
 * Left orbits L_i (i < O), right orbits R_j (j < O), each of size GN.
 * Dart e from i to j with label s gives edges L_{i,g} ~ R_{j,g*s} for all g.
 * Class (i,j) holds m_ij darts with distinct labels. For O = 2, m00 = m11 = x and
 * m01 = m10 = d - x, so every orbit has degree d. For O = 1, m00 = d (Haar).
 */

static int O, nd;
static int dfrom[MAXDD], dto[MAXDD], dS[MAXDD], dSinv[MAXDD];
static int cs[2][2], cm[2][2];
static int outL[2][MAXD], nout[2], inL[2][MAXD], nin[2];
static int dfwd[MAXDD][MAXN], dbwd[MAXDD][MAXN];

static void build_layout(int oo, int x) {
    O = oo;
    nd = 0;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) { cs[i][j] = 0; cm[i][j] = 0; }
    for (int i = 0; i < O; i++)
        for (int j = 0; j < O; j++) {
            int m = (O == 1) ? d : (i == j ? x : d - x);
            cs[i][j] = nd;
            cm[i][j] = m;
            for (int t = 0; t < m; t++) { dfrom[nd] = i; dto[nd] = j; nd++; }
        }
    for (int i = 0; i < 2; i++) { nout[i] = 0; nin[i] = 0; }
    for (int e = 0; e < nd; e++) {
        outL[dfrom[e]][nout[dfrom[e]]++] = e;
        inL[dto[e]][nin[dto[e]]++] = e;
    }
}

static void set_dart(int e, int s) {
    dS[e] = s;
    dSinv[e] = ginv(s);
    for (int g = 0; g < GN; g++) {
        dfwd[e][g] = gmul(g, s);
        dbwd[e][g] = gmul(g, dSinv[e]);
    }
}

/* True if label s is unused by the other darts of the same class as e. */
static int s_ok(int e, int s) {
    int i = dfrom[e], j = dto[e];
    for (int t = cs[i][j]; t < cs[i][j] + cm[i][j]; t++)
        if (t != e && dS[t] == s) return 0;
    return 1;
}

/* ------------------------------------------------------------ BFS and cost */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int VN = O * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < VN) {
                int i = v / GN, g = v % GN;
                for (int t = 0; t < nout[i]; t++) {
                    int e = outL[i][t];
                    int u = VN + dto[e] * GN + dfwd[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int r = v - VN, j = r / GN, h = r % GN;
                for (int t = 0; t < nin[j]; t++) {
                    int e = inL[j][t];
                    int u = dfrom[e] * GN + dbwd[e][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Each orbit is vertex-transitive under the group action, so one BFS per orbit
 * representative decides the diameter. */
static long cover_cost(void) {
    int VN = O * GN;
    int V = 2 * VN;
    long c = 0;
    for (int i = 0; i < O; i++) {
        c += (long)(V - bfs_count(i * GN));
        c += (long)(V - bfs_count(VN + i * GN));
    }
    return c;
}

/* One annealing restart on the current layout. Returns 1 if diameter <= D was reached. */
static int anneal(double until) {
    for (int e = 0; e < nd; e++) dS[e] = -1;
    for (int e = 0; e < nd; e++) {
        int x;
        do { x = rndint(GN); } while (!s_ok(e, x));
        set_dart(e, x);
    }
    long cost = cover_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    for (int it = 0; it < ITERS && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / ITERS);
        int e = rndint(nd);
        int x;
        do { x = rndint(GN); } while (!s_ok(e, x));
        int old = dS[e];
        set_dart(e, x);
        long c2 = cover_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            set_dart(e, old);
        }
    }
    return cost == 0;
}

/* Search one candidate (orbit count and group) until time 'until'.
 * For O = 2, each restart draws a fresh x in 1..d-1. */
static int search_cand(const Cand *cd, double until, int *outX, int *outS) {
    setup_group(cd->q, cd->p, cd->k, cd->c);
    while (now() < until) {
        int x = (cd->O == 2) ? 1 + rndint(d - 1) : 0;
        build_layout(cd->O, x);
        if (anneal(until)) {
            *outX = x;
            for (int e = 0; e < nd; e++) outS[e] = dS[e];
            return 1;
        }
    }
    return 0;
}

static void print_result(void) {
    int VN = O * GN;
    printf("%d %d\n", 2 * VN, nd * GN);
    for (int e = 0; e < nd; e++)
        for (int g = 0; g < GN; g++)
            printf("%d %d\n", dfrom[e] * GN + g, VN + dto[e] * GN + dfwd[e][g]);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V - y->V;
    return x->O - y->O;
}

static Cand cand[MAXCAND];
static int bestS[MAXDD], tS[MAXDD];

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
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    int nc = 0;
    for (int oo = 1; oo <= 2; oo++)
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 2; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                int N = q * c;
                if (N <= d || N > MAXN) continue;
                int V = 2 * oo * N;
                if (V < vlo || V > vhi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {oo, q, p, k, c, N, V};
                    cand[nc++] = cd;
                }
            }
        }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestIdx = -1, bestX = 0, bestV = 0, tX = 0;

    /* Phase 1: binary search for the largest feasible vertex count. Each probe
     * gets an equal share of the remaining time over the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (search_cand(&cand[mid], now() + slice, &tX, tS)) {
            if (cand[mid].V > bestV) {
                bestV = cand[mid].V;
                bestIdx = mid;
                bestX = tX;
                memcpy(bestS, tS, sizeof(int) * MAXDD);
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend the leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = bestIdx < 0 ? 0 : bestIdx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].V <= bestV) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (search_cand(&cand[idx], now() + slice, &tX, tS)) {
            bestV = cand[idx].V;
            bestIdx = idx;
            bestX = tX;
            memcpy(bestS, tS, sizeof(int) * MAXDD);
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[bestIdx].q, cand[bestIdx].p, cand[bestIdx].k, cand[bestIdx].c);
    build_layout(cand[bestIdx].O, bestX);
    for (int e = 0; e < nd; e++) set_dart(e, bestS[e]);
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

    # Multi-orbit affine lifts. The vertex count V lies in [vlo, vhi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        vlo = max(best[0] + 1, mb // 8)
        vhi = mb
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
