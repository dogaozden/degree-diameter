"""Multi-orbit group lifts for the bipartite degree-diameter problem.

The parent searched only single-orbit Haar graphs over F_q x| H. This version
searches a different family: lifts with kb base vertices on each side over a group G
(cyclic Z_N or affine F_q x| H). Base darts (i, j, g) join L_{i,x} to R_{j,xg}. Each
base vertex has exactly d darts, and darts between the same base pair have distinct
labels, so the lift is simple and d-regular. With kb = 1 the family contains the
parent's Haar graphs.

G acts on each fiber by left multiplication, so diameter <= D reduces to 2*kb BFS
runs, one from (b, e) for each base vertex b. The C engine anneals the dart labels,
then iterates from the incumbent by re-labelling two darts.

Safety: the Python side keeps a valid fallback. It runs an affine k=1 pass first, then
a multi-orbit pass that starts above the best graph found so far, and checks every
result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit group lift search.
 * Usage: prog d D seed time_limit minV maxV kmin kmax types
 *   types bit 1: cyclic groups Z_N; bit 2: affine groups F_q x| H.
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
#define MAXN 1600
#define MAXK 4
#define MAXD 16
#define MAXE (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 40000

typedef struct { int type, q, p, e, c, N, kb, V; } Cand;

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

static int factor_pp(int q, int *p, int *e) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *e = kk;
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

static void build_field(int q, int p, int e) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= e; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < e; i++)
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
        for (int i = 0; i < e; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, e, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, e, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ groups */

static int GN;
static int GM[MAXN][MAXN];
static int GI[MAXN];
static int PWG[MAXQ], Hel[MAXQ];

/* Cyclic: GM = addition mod N. Affine: element (a, h_j) coded as a*c + j,
 * product (a, h_j)(b, h_t) = (a + h_j b, h_j h_t), with h_j = g^(j (q-1)/c). */
static void build_group(const Cand *cd) {
    int N = cd->N;
    GN = N;
    if (cd->type == 0) {
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                GM[x][y] = (x + y) % N;
    } else {
        int q = cd->q, c = cd->c;
        build_field(q, cd->p, cd->e);
        int g = -1;
        for (int g0 = 2; g0 < q && g < 0; g0++) {
            int x = 1, ord = 0;
            do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
            if (ord == q - 1) g = g0;
        }
        PWG[0] = 1;
        for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
        int step = (q - 1) / c;
        for (int t = 0; t < c; t++) Hel[t] = PWG[(t * step) % (q - 1)];
        for (int x = 0; x < N; x++) {
            int a = x / c, j = x % c;
            for (int y = 0; y < N; y++) {
                int b = y / c, t = y % c;
                GM[x][y] = ADDT[a][MULT[Hel[j]][b]] * c + (j + t) % c;
            }
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GM[x][y] == 0) { GI[x] = y; break; }
}

/* ------------------------------------------------------------ lift state */

static int kb, E;
static int dI[MAXE], dJ[MAXE], lab[MAXE];
static int outD[MAXK][MAXD], inD[MAXK][MAXD];

/* Left base i is vertex i*N + x; right base j is vertex (kb+j)*N + y.
 * Dart e joins L_{dI,x} to R_{dJ, x*lab}. */
static void rebuild_index(void) {
    int ci[MAXK] = {0}, cj[MAXK] = {0};
    for (int e = 0; e < E; e++) {
        int i = dI[e], j = dJ[e];
        outD[i][ci[i]++] = e;
        inD[j][cj[j]++] = e;
    }
}

static int stamp_ = 0;
static int vis[MAXV], que[MAXV];

static int bfs_count(int src) {
    int N = GN, KN = kb * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / N, x = v % N;
                for (int t = 0; t < d; t++) {
                    int e = outD[i][t];
                    int u = KN + dJ[e] * N + GM[x][lab[e]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = (v - KN) / N, y = v % N;
                for (int t = 0; t < d; t++) {
                    int e = inD[j][t];
                    int u = dI[e] * N + GM[y][GI[lab[e]]];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fiber transitivity: BFS from one vertex of each base vertex suffices. */
static long cover_cost(void) {
    int V = 2 * kb * GN;
    long c = 0;
    for (int b = 0; b < 2 * kb; b++)
        c += (long)(V - bfs_count(b * GN));
    return c;
}

/* A label for dart e that differs from the labels of other darts on the same base pair. */
static int free_label(int e) {
    for (;;) {
        int x = rndint(GN), ok = 1;
        for (int f = 0; f < E && ok; f++)
            if (f != e && dI[f] == dI[e] && dJ[f] == dJ[e] && lab[f] == x) ok = 0;
        if (ok) return x;
    }
}

/* Random d-regular bipartite base pattern: the sum of d random permutation matrices. */
static void random_pattern(void) {
    int M[MAXK][MAXK];
    int perm[MAXK];
    memset(M, 0, sizeof M);
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < kb; i++) M[i][perm[i]]++;
    }
    E = 0;
    for (int i = 0; i < kb; i++)
        for (int j = 0; j < kb; j++)
            for (int m = 0; m < M[i][j]; m++) {
                dI[E] = i;
                dJ[E] = j;
                E++;
            }
    rebuild_index();
}

/* Iterated annealing: the first round starts random; later rounds start from the
 * incumbent with two darts re-labelled, at a lower starting temperature.
 * Returns 1 when cost 0 is reached (state holds the valid lift), 0 on timeout. */
static int search_group(double until) {
    const int iters = 4000;
    int have = 0;
    long bestc = 0;
    int incD[MAXE], incJ[MAXE], incL[MAXE];
    while (now() < until) {
        if (!have) {
            random_pattern();
            for (int e = 0; e < E; e++) lab[e] = -1;
            for (int e = 0; e < E; e++) lab[e] = free_label(e);
        } else {
            memcpy(dI, incD, sizeof(int) * (size_t)E);
            memcpy(dJ, incJ, sizeof(int) * (size_t)E);
            memcpy(lab, incL, sizeof(int) * (size_t)E);
            rebuild_index();
            for (int t = 0; t < 2; t++) {
                int e = rndint(E);
                lab[e] = free_label(e);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(E);
            int old = lab[e];
            lab[e] = free_label(e);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                lab[e] = old;
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incD, dI, sizeof(int) * (size_t)E);
            memcpy(incJ, dJ, sizeof(int) * (size_t)E);
            memcpy(incL, lab, sizeof(int) * (size_t)E);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int type, int q, int p, int e, int c, int N, int kbase) {
    if (nc < MAXCAND) {
        Cand x = {type, q, p, e, c, N, kbase, 2 * kbase * N};
        cand[nc++] = x;
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    return x->N - y->N;
}

/* ------------------------------------------------------------ main */

static int solFound = 0;
static Cand solC;
static int solE;
static int solDI[MAXE], solDJ[MAXE], solLAB[MAXE];

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minV = atoi(argv[5]), maxV = atoi(argv[6]);
    int kmin = atoi(argv[7]), kmax = atoi(argv[8]);
    int types = atoi(argv[9]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (kmin < 1) kmin = 1;
    if (kmax > MAXK) kmax = MAXK;
    if (kmin > kmax) { printf("0 0\n"); return 0; }

    for (int kbase = kmin; kbase <= kmax; kbase++) {
        int Nlo = (minV + 2 * kbase - 1) / (2 * kbase);
        int Nhi = maxV / (2 * kbase);
        if (Nlo < d + 1) Nlo = d + 1;
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nlo > Nhi) continue;
        if (types & 1)
            for (int N = Nlo; N <= Nhi; N++)
                add_cand(0, 0, 0, 0, 0, N, kbase);
        if (types & 2) {
            for (int q = 3; q < MAXQ; q++) {
                int p, e;
                if (!factor_pp(q, &p, &e)) continue;
                for (int c = 1; c <= q - 1; c++) {
                    if ((q - 1) % c) continue;
                    int N = q * c;
                    if (N < Nlo || N > Nhi) continue;
                    add_cand(1, q, p, e, c, N, kbase);
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestV = 0;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].V <= bestV) continue;
        double slice = 0.08 * rem;
        if (slice < 0.6) slice = 0.6;
        if (slice > 5.0) slice = 5.0;
        if (slice > rem) slice = rem;
        build_group(&cand[ci]);
        kb = cand[ci].kb;
        E = kb * d;
        if (search_group(now() + slice)) {
            bestV = cand[ci].V;
            solFound = 1;
            solC = cand[ci];
            solE = E;
            memcpy(solDI, dI, sizeof(int) * (size_t)E);
            memcpy(solDJ, dJ, sizeof(int) * (size_t)E);
            memcpy(solLAB, lab, sizeof(int) * (size_t)E);
        }
    }

    if (!solFound) {
        printf("0 0\n");
        return 0;
    }
    build_group(&solC);
    kb = solC.kb;
    E = solE;
    memcpy(dI, solDI, sizeof(int) * (size_t)E);
    memcpy(dJ, solDJ, sizeof(int) * (size_t)E);
    memcpy(lab, solLAB, sizeof(int) * (size_t)E);
    rebuild_index();
    if (cover_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int N = GN;
    printf("%d %d\n", 2 * kb * N, kb * N * d);
    for (int i = 0; i < kb; i++)
        for (int x = 0; x < N; x++)
            for (int t = 0; t < d; t++) {
                int e = outD[i][t];
                printf("%d %d\n", i * N + x, (kb + dJ[e]) * N + GM[x][lab[e]]);
            }
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


def _run_search(d, D, seed, budget, lo, hi, kmin, kmax, types):
    """Run the C engine on total-vertex window [lo, hi] and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, kmin, kmax, types],
                     stdin_graph=None, timeout=budget + 6.0)
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
        hi = mb // 2

        def remaining():
            return 0.86 * time_limit - (time.monotonic() - t0) - 1.5

        # Pass A: single-orbit affine lifts, the parent's family, as a safety net.
        budget = remaining()
        lo = max(best[0] + 2, mb // 4)
        if budget > 3.0 and lo <= hi:
            try:
                consider(_run_search(d, D, seed, 0.4 * budget, lo, hi, 1, 1, 2))
            except Exception:
                pass

        # Pass B: multi-orbit lifts (kb = 2..4 base vertices per side), above the incumbent.
        budget = remaining()
        lo = max(best[0] + 2, mb // 4)
        if budget > 3.0 and lo <= hi:
            try:
                consider(_run_search(d, D, seed + 1, budget, lo, hi, 2, 4, 3))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
