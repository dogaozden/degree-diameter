"""Two-orbit bi-Cayley lift search for the bipartite degree-diameter problem.

New in this version: the C engine searches block-voltage lifts over a group G of
order N, with two kinds of base structure:

* mode 1: one left orbit and one right orbit, voltage set S of size d (Haar graph,
  2N vertices). This is the parent's family.
* mode 2: two left orbits and two right orbits with block matrix
  [[x, d-x], [d-x, x]], x = floor(d/2). Left vertex L(a,g) is joined to
  R(b, g*s) for each voltage s in block (a,b). This has 4N vertices, is d-regular and
  simple, and needs only 2 BFS runs per orbit representative (4 in total).

Groups: cyclic Z_N for every N (fine-grained orders) and the affine groups
F_q x| H with |H| = c | q-1 (non-abelian). Candidates are ordered by total vertex
count, and the first attempt at each total-size is the cheapest one to succeed.

The annealing is iterated from the incumbent, as in the parent, and each block
entry is kept distinct within its block so the graph stays simple.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit bi-Cayley lift search.
 * Usage: prog d D seed time_limit tlo thi
 *   tlo, thi: range of total vertex counts to consider.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 *
 * Left vertex L(a,g) = a*N + g (a < NA); right vertex R(b,h) = NA*N + b*N + h.
 * Block (a,b) has M[a][b] voltages s; L(a,g) ~ R(b, g*s).
 * Left translations are automorphisms, so diameter <= D is checked from one
 * representative per orbit: L(a,e) for each a, and R(b,e) for each b.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXN 2500
#define MAXD 32
#define NB 2
#define MAXV (2 * NB * MAXN)
#define MAXCAND 20000

typedef struct { int na, type, N, q, p, k, c; long total; } Cand;

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

/* ------------------------------------------------------------ groups */

static int GN, NA, LO;
static uint16_t MT[MAXN * MAXN];   /* MT[x*GN + y] = x*y */
static uint16_t INVT[MAXN];

static void build_cyclic(int N) {
    GN = N;
    for (int x = 0; x < N; x++) {
        uint16_t *row = &MT[x * N];
        for (int y = 0; y < N; y++) {
            int s = x + y;
            row[y] = (uint16_t)(s >= N ? s - N : s);
        }
        INVT[x] = (uint16_t)(x ? N - x : 0);
    }
}

/* Element (a, h_j) is coded as a*c + j; (a,h_j)(b,h_t) = (a + h_j*b, h_j*h_t). */
static void build_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    int g = 0;
    for (int g0 = 2; g0 < q && !g; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    int PWG[MAXQ], Hel[MAXQ], hidx[MAXQ];
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    int N = q * c;
    GN = N;
    int yb[MAXN], yt[MAXN];
    for (int y = 0; y < N; y++) { yb[y] = y / c; yt[y] = y % c; }
    for (int x = 0; x < N; x++) {
        int a = x / c, j = x % c;
        uint16_t *row = &MT[x * N];
        for (int y = 0; y < N; y++) {
            int na = ADDT[a][MULT[Hel[j]][yb[y]]];
            int nt = hidx[MULT[Hel[j]][Hel[yt[y]]]];
            row[y] = (uint16_t)(na * c + nt);
        }
    }
    for (int x = 0; x < N; x++) {
        INVT[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = (uint16_t)y; break; }
    }
}

/* ------------------------------------------------------------ block-voltage lift state */

static int M[NB][NB];
static int VOL[NB][NB][MAXD], bestVOL[NB][NB][MAXD], incV[NB][NB][MAXD];
static uint16_t FW[NB][NB][MAXD][MAXN], BW[NB][NB][MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void setup_blocks(int na, int dd) {
    memset(M, 0, sizeof M);
    if (na == 1) {
        M[0][0] = dd;
    } else {
        int x = dd / 2;
        M[0][0] = x;
        M[1][1] = x;
        M[0][1] = dd - x;
        M[1][0] = dd - x;
    }
}

static void set_vol(int a, int b, int k, int s) {
    int N = GN;
    VOL[a][b][k] = s;
    int si = INVT[s];
    uint16_t *f = FW[a][b][k], *w = BW[a][b][k];
    for (int g = 0; g < N; g++) {
        f[g] = MT[g * N + s];
        w[g] = MT[g * N + si];
    }
}

static int in_block(int a, int b, int x, int cnt) {
    for (int i = 0; i < cnt; i++)
        if (VOL[a][b][i] == x) return 1;
    return 0;
}

static void init_block(int a, int b) {
    for (int k = 0; k < M[a][b]; k++) {
        int x;
        do { x = rndint(GN); } while (in_block(a, b, x, k));
        set_vol(a, b, k, x);
    }
}

static void move_entry(int a, int b, int k) {
    int x;
    do { x = rndint(GN); } while (in_block(a, b, x, M[a][b]));
    set_vol(a, b, k, x);
}

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
            if (v < LO) {
                int a = v / N, g = v - a * N;
                for (int b = 0; b < NB; b++)
                    for (int k = 0; k < M[a][b]; k++) {
                        int u = LO + b * N + FW[a][b][k][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            } else {
                int w = v - LO;
                int b = w / N, h = w - b * N;
                for (int a = 0; a < NB; a++)
                    for (int k = 0; k < M[a][b]; k++) {
                        int u = a * N + BW[a][b][k][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
            }
        }
    }
    return tail;
}

/* Sum over orbit representatives of uncovered vertices (0 iff diameter <= D). */
static long cover_cost(void) {
    long V = 2L * LO, c = 0;
    for (int a = 0; a < NA; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < NA; b++) c += V - bfs_count(LO + b * GN);
    return c;
}

static void init_all(void) {
    for (int a = 0; a < NA; a++)
        for (int b = 0; b < NA; b++) init_block(a, b);
}

static void restore_all(void) {
    for (int a = 0; a < NA; a++)
        for (int b = 0; b < NA; b++)
            for (int k = 0; k < M[a][b]; k++) set_vol(a, b, k, incV[a][b][k]);
}

/* Iterated annealing: restart rounds from the incumbent with two entries moved,
 * at a lower starting temperature. Returns 1 on cost 0, 0 on timeout. */
static int search_group(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            init_all();
        } else {
            restore_all();
            for (int t = 0; t < 2; t++) {
                int a = rndint(NA), b = rndint(NA), k = rndint(M[a][b]);
                move_entry(a, b, k);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int a = rndint(NA), b = rndint(NA), k = rndint(M[a][b]);
            int old = VOL[a][b][k];
            move_entry(a, b, k);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T))
                cost = c2;
            else
                set_vol(a, b, k, old);
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incV, VOL, sizeof VOL);
        }
    }
    return 0;
}

static int cmp_cand(const void *A, const void *B) {
    const Cand *x = (const Cand *)A, *y = (const Cand *)B;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
    if (x->type != y->type) return y->type - x->type;   /* affine first */
    return x->na - y->na;
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long tlo = atol(argv[5]), thi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    int nc = 0;
    for (int na = 1; na <= NB; na++) {
        long mult = 2L * na;                 /* vertices per group element */
        long nlo = (tlo + mult - 1) / mult, nhi = thi / mult;
        if (nlo < 2L * d + 2) nlo = 2L * d + 2;
        if (nhi > MAXN) nhi = MAXN;
        for (long N = nlo; N <= nhi; N++)
            if (nc < MAXCAND) {
                Cand cd = {na, 0, (int)N, 0, 0, 0, 0, mult * N};
                cand[nc++] = cd;
            }
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 2; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                if (N < nlo || N > nhi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {na, 1, (int)N, q, p, k, c, mult * N};
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    long bestTotal = 0;
    int bestCi = -1;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand *cd = &cand[ci];
        if (cd->total <= bestTotal) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (cd->type) build_affine(cd->q, cd->p, cd->k, cd->c);
        else build_cyclic(cd->N);
        NA = cd->na;
        LO = NA * GN;
        setup_blocks(NA, d);
        if (search_group(now() + slice)) {
            bestTotal = cd->total;
            bestCi = ci;
            memcpy(bestVOL, VOL, sizeof VOL);
        }
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand *cd = &cand[bestCi];
    if (cd->type) build_affine(cd->q, cd->p, cd->k, cd->c);
    else build_cyclic(cd->N);
    NA = cd->na;
    LO = NA * GN;
    setup_blocks(NA, d);
    for (int a = 0; a < NB; a++)
        for (int b = 0; b < NB; b++)
            for (int k = 0; k < M[a][b]; k++)
                set_vol(a, b, k, bestVOL[a][b][k]);
    printf("%d %ld\n", 2 * LO, (long)NA * GN * d);
    for (int a = 0; a < NA; a++)
        for (int g = 0; g < GN; g++)
            for (int b = 0; b < NA; b++)
                for (int k = 0; k < M[a][b]; k++)
                    printf("%d %d\n", a * GN + g, LO + b * GN + FW[a][b][k][g]);
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

    # Search: two-orbit and one-orbit block-voltage lifts over cyclic and affine groups.
    # Only total vertex counts in [tlo, thi] are considered, and tlo starts above the
    # best graph so far.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        tlo = max(best[0] + 1, mb // 5)
        thi = mb
        if budget > 2.0 and tlo <= thi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tlo, thi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
