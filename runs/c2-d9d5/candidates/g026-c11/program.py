"""Multi-orbit voltage lifts over finite groups for the bipartite degree-diameter problem.

New construction: the C engine searches lifts with B left orbits and B right orbits
(B = 1, 2, 3) over a finite group G of order N. G is cyclic, F_q x| H (H the subgroup of
order c of F_q^*), or elementary abelian F_q. Left orbit i and right orbit j are joined by
M[i][j] darts, where M is a nonnegative integer matrix with all row and column sums d
(a sum of d random permutation matrices). A dart with voltage s joins L_{i,g} to R_{j,g*s}.
The graph has 2*B*N vertices, is d-regular and bipartite, and is simple, because darts
between the same orbit pair get distinct voltages.

Left and right multiplication by G are automorphisms, and each orbit is regular. So the
diameter test reduces to 2B BFS runs, one from the identity of each orbit. Candidates are
tried in ascending order of total order, skipping any at or below the incumbent. B = 1 is the
old Haar family, so that family stays available.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search over finite groups.
 * Usage: prog d D seed time_limit minT maxT     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 257
#define MAXN 2048
#define MAXB 3
#define MAXD 32
#define MAXDARTS (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXE (MAXB * MAXD * MAXN)
#define MAXCAND 80000
#define ITERS 8000

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

/* ------------------------------------------------------------ group tables */

static unsigned short MT[MAXN][MAXN];   /* product table, x*y */
static int INV[MAXN];
static int HEL[MAXQ];
static int PWG[MAXQ];
static int N, B, LN, V, nd;

/* type 0: cyclic Z_n. type 1: F_q x| H with |H| = c, element (a, h_j) coded a*c + j,
 * product (a, h_j)(b, h_t) = (a + h_j*b, h_j h_t), and h_j h_t = h_{(j+t) mod c}.
 * c = 1 gives the elementary abelian group F_q. Identity is code 0 in both types. */
static int build_group(int type, int n, int q, int p, int k, int c) {
    N = n;
    if (type == 0) {
        for (int x = 0; x < n; x++) {
            for (int y = 0; y < n; y++) {
                int s = x + y;
                if (s >= n) s -= n;
                MT[x][y] = (unsigned short)s;
            }
            INV[x] = (n - x) % n;
        }
        return 1;
    }
    build_field(q, p, k);
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) return 0;
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < c; j++) HEL[j] = PWG[(j * step) % (q - 1)];
    for (int x = 0; x < n; x++) {
        int a = x / c, j = x % c;
        for (int y = 0; y < n; y++) {
            int b = y / c, t = y % c;
            int na = ADDT[a][MULT[HEL[j]][b]];
            int nt = (j + t) % c;
            MT[x][y] = (unsigned short)(na * c + nt);
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
    return 1;
}

/* ------------------------------------------------------------ lift state */

static int M[MAXB][MAXB];
static int DL[MAXDARTS], DR[MAXDARTS], SV[MAXDARTS];
static int FW[MAXDARTS][MAXN], BW[MAXDARTS][MAXN];
static int LD[MAXB][MAXD], RD[MAXB][MAXD];

static void setdart(int k, int x) {
    SV[k] = x;
    int xi = INV[x];
    for (int g = 0; g < N; g++) {
        FW[k][g] = MT[g][x];       /* L_{i,g} ~ R_{j, g*x} */
        BW[k][g] = MT[g][xi];      /* R_{j,h} ~ L_{i, h*x^-1} */
    }
}

/* Random B x B matrix with all row and column sums d: sum of d random permutation matrices. */
static void make_matrix(void) {
    memset(M, 0, sizeof M);
    int perm[MAXB];
    for (int r = 0; r < d; r++) {
        for (int i = 0; i < B; i++) perm[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < B; i++) M[i][perm[i]]++;
    }
}

static void make_darts(void) {
    nd = 0;
    for (int i = 0; i < B; i++)
        for (int j = 0; j < B; j++)
            for (int t = 0; t < M[i][j]; t++) {
                DL[nd] = i;
                DR[nd] = j;
                nd++;
            }
    int cl[MAXB] = {0}, cr[MAXB] = {0};
    for (int k = 0; k < nd; k++) {
        LD[DL[k]][cl[DL[k]]++] = k;
        RD[DR[k]][cr[DR[k]]++] = k;
    }
}

/* True if voltage x for dart k clashes with another dart k2 < lim on the same orbit pair. */
static int conflict(int k, int x, int lim) {
    for (int k2 = 0; k2 < lim; k2++)
        if (k2 != k && DL[k2] == DL[k] && DR[k2] == DR[k] && SV[k2] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------ BFS cost */

static int VIS[MAXV], QUE[MAXV];
static int stamp_ = 0;

/* Vertices: left orbit i, element g -> i*N+g; right orbit j, element h -> LN + j*N + h. */
static int bfs_cnt(int src) {
    stamp_++;
    int head = 0, tail = 0;
    QUE[tail++] = src;
    VIS[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = QUE[head++];
            if (v < LN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < d; t++) {
                    int k = LD[i][t];
                    int u = LN + DR[k] * N + FW[k][g];
                    if (VIS[u] != stamp_) { VIS[u] = stamp_; QUE[tail++] = u; }
                }
            } else {
                int r = v - LN;
                int j = r / N, h = r - j * N;
                for (int t = 0; t < d; t++) {
                    int k = RD[j][t];
                    int u = DL[k] * N + BW[k][h];
                    if (VIS[u] != stamp_) { VIS[u] = stamp_; QUE[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Orbits are regular under G, so BFS from the identity of each orbit covers all pairs. */
static long cover_cost(void) {
    long c = 0;
    for (int i = 0; i < B; i++) c += (long)(V - bfs_cnt(i * N));
    for (int j = 0; j < B; j++) c += (long)(V - bfs_cnt(LN + j * N));
    return c;
}

/* ------------------------------------------------------------ search */

static void random_state(void) {
    for (int k = 0; k < nd; k++) {
        int x;
        do { x = rndint(N); } while (conflict(k, x, k));
        setdart(k, x);
    }
}

/* Iterated annealing over all dart voltages. The first round starts from a random state.
 * Later rounds restart from the incumbent with two voltages replaced, at a lower
 * starting temperature. Returns 1 when cost 0 is reached, 0 on timeout. */
static int search(double until) {
    int have = 0;
    long bestc = 0;
    int inc[MAXDARTS];
    while (now() < until) {
        if (!have) {
            random_state();
        } else {
            for (int k = 0; k < nd; k++) setdart(k, inc[k]);
            for (int t = 0; t < 2; t++) {
                int k = rndint(nd), x;
                do { x = rndint(N); } while (conflict(k, x, nd));
                setdart(k, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int k = rndint(nd), x;
            do { x = rndint(N); } while (x == SV[k] || conflict(k, x, nd));
            int old = SV[k];
            setdart(k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                setdart(k, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(inc, SV, sizeof(int) * (size_t)nd);
        }
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static int BESTV = 0, BESTM = 0;
static int BESTE[2 * MAXE];

static void store_best(void) {
    int m = 0;
    for (int k = 0; k < nd; k++)
        for (int g = 0; g < N; g++) {
            BESTE[2 * m] = DL[k] * N + g;
            BESTE[2 * m + 1] = LN + DR[k] * N + FW[k][g];
            m++;
        }
    BESTM = m;
    BESTV = V;
}

/* ------------------------------------------------------------ candidates */

typedef struct { int B, type, N, q, p, k, c, total; } Cand;
static Cand CAND[MAXCAND];
static int NC = 0;

static void add_cand(int b, int type, int n, int q, int p, int k, int c, int minT, int maxT) {
    int tot = 2 * b * n;
    if (tot < minT || tot > maxT) return;
    if (n < d || n > MAXN) return;
    if (NC >= MAXCAND) return;
    Cand cd = {b, type, n, q, p, k, c, tot};
    CAND[NC++] = cd;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
    if (x->type != y->type) return y->type - x->type;   /* affine before cyclic */
    return x->B - y->B;
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
    int minT = atoi(argv[5]), maxT = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (minT < 2 * d) minT = 2 * d;

    /* Enumerate (B, group) candidates whose total order lies in [minT, maxT]. */
    for (int b = 1; b <= MAXB; b++) {
        int lo = (minT + 2 * b - 1) / (2 * b);
        int hi = maxT / (2 * b);
        if (hi > MAXN) hi = MAXN;
        if (lo < d) lo = d;
        for (int n = lo; n <= hi; n++) add_cand(b, 0, n, 0, 0, 0, 0, minT, maxT);
    }
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            if (c == 1 && k == 1) continue;          /* same as cyclic Z_q */
            int n = q * c;
            if (n > MAXN) continue;
            for (int b = 1; b <= MAXB; b++)
                add_cand(b, 1, n, q, p, k, c, minT, maxT);
        }
    }
    qsort(CAND, (size_t)NC, sizeof(Cand), cmp_cand);

    /* Ascending order: skip anything not above the incumbent. Each attempt gets 20% of
     * the remaining time, at least 1 s. */
    int bestT = 0;
    for (int ci = 0; ci < NC; ci++) {
        Cand cd = CAND[ci];
        if (cd.total <= bestT) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (!build_group(cd.type, cd.N, cd.q, cd.p, cd.k, cd.c)) continue;
        B = cd.B;
        LN = B * N;
        V = 2 * LN;
        make_matrix();
        make_darts();
        if (search(now() + slice)) {
            bestT = V;
            store_best();
        }
    }

    if (BESTV == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", BESTV, BESTM);
    for (int m = 0; m < BESTM; m++)
        printf("%d %d\n", BESTE[2 * m], BESTE[2 * m + 1]);
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

    # Multi-orbit voltage lifts over finite groups, ascending in total order.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        minT = max(best[0] + 1, mb // 4)
        maxT = mb
        if budget > 2.0 and minT <= maxT:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), minT, maxT],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
