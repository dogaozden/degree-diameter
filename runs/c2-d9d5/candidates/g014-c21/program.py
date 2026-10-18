"""Multi-orbit voltage lifts over small groups for the bipartite degree-diameter problem.

New construction in this version: a bi-Cayley graph with b orbits per side.
Let G be a group of order N (affine group F_q x| H, or cyclic Z_N). Left vertices
are L_{i,g} and right vertices are R_{j,h}, for i, j in 0..b-1 and g, h in G. Let M be a
b x b matrix of nonnegative integers with all row sums and column sums equal to d
(built as a sum of d random permutation matrices). For each pair (i, j) choose M[i][j]
distinct voltages S_ij in G, and join L_{i,g} to R_{j, g*s} for every s in S_ij.

The graph is bipartite and simple, has order 2bN, and is d-regular. Left multiplication
by G is an automorphism that acts regularly on each fiber, so diameter <= D is checked
with 2b BFS runs, from L_{i,e} and R_{j,e}. The b = 1 case is the single-orbit affine
Haar lift from the parent. Larger b gives orders 2bN for group orders N that
single-orbit lifts cannot reach, so the search has many more candidate orders near
the record.

Search: simulated annealing over the voltages for each candidate (group, b). Candidates
are sorted by order and searched by binary search with equal time slices, then by a
short phase that tries the next larger orders. Every returned graph is checked with
lib.is_valid. Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d}
fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo and hi bound the vertex count 2*b*N of candidates.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 1400
#define MAXN 1400
#define MAXB 3
#define MAXD 32
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 12000
#define MAXSLOT (MAXB * MAXD)

typedef struct { int type, q, p, k, c, N, b, T; } Cand;

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

static int16_t ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ];
static int NEGT[MAXQ];
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

/* Multiply field elements a, b (base-p digit vectors) modulo the monic f with digits m. */
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
            ADDT[a][b] = (int16_t)r;
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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0; /* zero divisor: reducible */
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = (int16_t)polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ groups */

static int GN;
static int16_t MT[MAXN][MAXN];
static int INVG[MAXN];

static int primitive_root(int q) {
    for (int g0 = 2; g0 < q; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) return g0;
    }
    return -1;
}

/* Affine group F_q x| H with |H| = c: element (a, h_j) coded as a*c + j.
 * Product (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void build_group_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int g = primitive_root(q);
    static int PW[MAXQ], Hel[MAXQ], hidx[MAXQ];
    PW[0] = 1;
    for (int i = 1; i < q - 1; i++) PW[i] = MULT[PW[i - 1]][g];
    int step = (q - 1) / c;
    for (int t = 0; t < c; t++) {
        Hel[t] = PW[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    GN = q * c;
    for (int x = 0; x < GN; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < GN; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[Hel[j]][b]];
            int nj = hidx[MULT[Hel[j]][Hel[t]]];
            MT[x][y] = (int16_t)(na * c + nj);
        }
    }
}

static void build_group_cyclic(int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x][y] = (int16_t)((x + y) % N);
}

static void build_inverses(void) {
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT[x][y] == 0) { INVG[x] = y; break; }
}

/* ------------------------------------------------------------ lift state */

static int BB, NN;
static int Mm[MAXB][MAXB];
static int Vs[MAXB][MAXB][MAXD];
static int bestM[MAXB][MAXB];
static int bestV[MAXB][MAXB][MAXD];
static int slotI[MAXSLOT], slotJ[MAXSLOT], slotT[MAXSLOT];
static int NSLOT;
static int vstamp[MAXV], qbuf[MAXV];
static int stampc = 0;
static Cand cand[MAXCAND];
static int nc = 0;

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) build_group_affine(cd->q, cd->p, cd->k, cd->c);
    else build_group_cyclic(cd->N);
    build_inverses();
    BB = cd->b;
    NN = GN;
}

/* Random b x b matrix with all row and column sums d: a sum of d permutation matrices. */
static void random_matrix(void) {
    memset(Mm, 0, sizeof Mm);
    for (int r = 0; r < d; r++) {
        int perm[MAXB];
        for (int i = 0; i < BB; i++) perm[i] = i;
        for (int i = BB - 1; i > 0; i--) {
            int k = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[k]; perm[k] = tmp;
        }
        for (int i = 0; i < BB; i++) Mm[i][perm[i]]++;
    }
    NSLOT = 0;
    for (int i = 0; i < BB; i++)
        for (int j = 0; j < BB; j++)
            for (int t = 0; t < Mm[i][j]; t++) {
                slotI[NSLOT] = i;
                slotJ[NSLOT] = j;
                slotT[NSLOT] = t;
                NSLOT++;
            }
}

/* Voltages within each (i, j) list must be distinct. */
static int pick_new(int i, int j, int t) {
    for (;;) {
        int x = rndint(NN);
        int ok = 1;
        for (int t2 = 0; t2 < Mm[i][j]; t2++)
            if (t2 != t && Vs[i][j][t2] == x) { ok = 0; break; }
        if (ok) return x;
    }
}

static void random_voltages(void) {
    for (int k = 0; k < NSLOT; k++) {
        int i = slotI[k], j = slotJ[k], t = slotT[k];
        int x;
        for (;;) {
            x = rndint(NN);
            int ok = 1;
            for (int t2 = 0; t2 < t; t2++)
                if (Vs[i][j][t2] == x) { ok = 0; break; }
            if (ok) break;
        }
        Vs[i][j][t] = x;
    }
}

/* Vertices: L_{i,g} = i*NN + g, R_{j,h} = BB*NN + j*NN + h.
 * Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int bn = BB * NN;
    stampc++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    vstamp[src] = stampc;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = qbuf[head++];
            if (v < bn) {
                int i = v / NN, g = v - i * NN;
                for (int j = 0; j < BB; j++) {
                    int m = Mm[i][j];
                    for (int t = 0; t < m; t++) {
                        int u = bn + j * NN + MT[g][Vs[i][j][t]];
                        if (vstamp[u] != stampc) { vstamp[u] = stampc; qbuf[tail++] = u; }
                    }
                }
            } else {
                int w = v - bn;
                int j = w / NN, h = w - j * NN;
                for (int i = 0; i < BB; i++) {
                    int m = Mm[i][j];
                    for (int t = 0; t < m; t++) {
                        int u = i * NN + MT[h][INVG[Vs[i][j][t]]];
                        if (vstamp[u] != stampc) { vstamp[u] = stampc; qbuf[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* Left and right fibers are each a single orbit under G, so 2b BFS runs decide the diameter. */
static long total_cost(void) {
    int V = 2 * BB * NN;
    long c = 0;
    for (int i = 0; i < BB; i++) c += (long)(V - bfs_reach(i * NN));
    for (int j = 0; j < BB; j++) c += (long)(V - bfs_reach(BB * NN + j * NN));
    return c;
}

static void save_best(void) {
    memcpy(bestM, Mm, sizeof Mm);
    memcpy(bestV, Vs, sizeof Vs);
}

/* Simulated annealing over voltages, with random restarts of matrix and voltages.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_cand(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_matrix();
        random_voltages();
        long cost = total_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(NSLOT);
            int i = slotI[k], j = slotJ[k], t = slotT[k];
            int old = Vs[i][j][t];
            Vs[i][j][t] = pick_new(i, j, t);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                Vs[i][j][t] = old;
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_graph(int M[MAXB][MAXB], int V_[MAXB][MAXB][MAXD]) {
    int bn = BB * NN;
    printf("%d %d\n", 2 * bn, bn * d);
    for (int i = 0; i < BB; i++)
        for (int g = 0; g < NN; g++)
            for (int j = 0; j < BB; j++)
                for (int t = 0; t < M[i][j]; t++)
                    printf("%d %d\n", i * NN + g, bn + j * NN + MT[g][V_[i][j][t]]);
}

static int cand_cmp(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->T != y->T) return x->T - y->T;
    return x->type - y->type;
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

    /* Candidates: orders T = 2*b*N for b orbits per side and group G of order N. */
    for (int b = 1; b <= MAXB; b++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                int N = q * c;
                if (N < 2 * d || N > MAXN) continue;
                int T = 2 * b * N;
                if (T <= lo || T > hi || nc >= MAXCAND) continue;
                Cand cd = {0, q, p, k, c, N, b, T};
                cand[nc++] = cd;
            }
        }
        for (int N = 2 * d; N <= MAXN; N++) {
            int T = 2 * b * N;
            if (T <= lo || T > hi || nc >= MAXCAND) continue;
            Cand cd = {1, 0, 0, 0, 0, N, b, T};
            cand[nc++] = cd;
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cand_cmp);

    int best_idx = -1, bestT = 0;

    /* Phase 1: binary search over sorted orders. Each probe gets an equal share of
     * the remaining time divided by the probes still needed. */
    int lo_i = 0, hi_i = nc - 1;
    while (lo_i <= hi_i && now() < t_end) {
        int mid = (lo_i + hi_i) / 2;
        int span = hi_i - lo_i + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[mid]);
        if (search_cand(now() + slice)) {
            best_idx = mid;
            bestT = cand[mid].T;
            save_best();
            lo_i = mid + 1;
        } else {
            hi_i = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few orders above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].T <= bestT) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        setup_cand(&cand[idx]);
        if (search_cand(now() + slice)) {
            best_idx = idx;
            bestT = cand[idx].T;
            save_best();
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
    setup_cand(&cand[best_idx]);
    print_graph(bestM, bestV);
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

    # Multi-orbit voltage lifts. The C search takes vertex-count bounds [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
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
