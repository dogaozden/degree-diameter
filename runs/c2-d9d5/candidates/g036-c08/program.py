"""Group voltage lifts with one or two base vertices per side, for the bipartite degree-diameter problem.

Bold change: the parent searched only Haar graphs (one left and one right base vertex, d darts).
This version adds a second family. Take G = F_q x| H, where H is the subgroup of F_q^* of order c
(c | q-1, c >= 1). The base graph has B in {1, 2} vertices per side. For B = 2 the dart matrix is
[[x, d-x], [d-x, x]] with 1 <= x <= d/2, so every base vertex has degree d and the base is connected.
Each dart (i, j) carries a group voltage s, and L_{i,g} ~ R_{j, g*s}. The lift has 2*B*|G| vertices
and is d-regular and bipartite. Left translations are automorphisms, so the diameter check reduces
to 2B BFS runs, one from each base vertex's identity element.

The C engine sorts all (q, c, B, x) candidates by vertex count, then tries them in ascending order
with simulated annealing on the voltages. Parallel darts within one base pair must have distinct
voltages. Candidates at or below the current best are skipped, and failed candidates are retried in
later passes. The Haar case (B = 1) is still in the candidate list, so the parent's family remains
covered. Python keeps the old constructions and K_{d,d} as fallbacks, and every result passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Group voltage lift search with B = 1 or 2 base vertices per side.
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
#define MAXT 64
#define MAXV (4 * MAXN)
#define MAXCAND 20000

typedef struct { int q, p, k, c, N, B, x; } Cand;

static int d, D, BB;
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

/* ------------------------------------------------------------ voltage lift state */

/* Darts: dart t joins left base dl[t] to right base dr[t] with voltage sv[t].
 * Left vertex (i, g) = i*N + g. Right vertex (j, h) = BB*N + j*N + h.
 * Edge: (i, g) ~ (j, g * sv[t]).
 */
static int T;
static int dl[MAXT], dr[MAXT], dcls[MAXT];
static int ldart[2][MAXD], rdart[2][MAXD];
static int sv[MAXT], svinv[MAXT];
static int fwd[MAXT][MAXN], bwd[MAXT][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_darts(int x) {
    int M[2][2] = {{0, 0}, {0, 0}};
    if (BB == 1) M[0][0] = d;
    else { M[0][0] = x; M[0][1] = d - x; M[1][0] = d - x; M[1][1] = x; }
    T = 0;
    int cnt[2] = {0, 0}, rc[2] = {0, 0};
    for (int i = 0; i < BB; i++)
        for (int j = 0; j < BB; j++)
            for (int m = 0; m < M[i][j]; m++) {
                dl[T] = i;
                dr[T] = j;
                dcls[T] = i * 2 + j;
                ldart[i][cnt[i]++] = T;
                rdart[j][rc[j]++] = T;
                T++;
            }
    for (int t = 0; t < T; t++) sv[t] = -1;
}

static void set_v(int t, int g) {
    int N = GN;
    sv[t] = g;
    svinv[t] = ginv(g);
    for (int h = 0; h < N; h++) {
        fwd[t][h] = gmul(h, g);
        bwd[t][h] = gmul(h, svinv[t]);
    }
}

/* True if g is unused by every other dart in the same base class. */
static int free_val(int t, int g) {
    for (int u = 0; u < T; u++)
        if (u != t && dcls[u] == dcls[t] && sv[u] == g) return 0;
    return 1;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, BN = BB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int k = 0; k < d; k++) {
                    int t = ldart[i][k];
                    int u = BN + dr[t] * N + fwd[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int j = w / N, h = w % N;
                for (int k = 0; k < d; k++) {
                    int t = rdart[j][k];
                    int u = dl[t] * N + bwd[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left and right translations are automorphisms, so one BFS per base vertex decides diameter. */
static long cover_cost(void) {
    int N = GN, BN = BB * N;
    long V = 2L * BN;
    long c = 0;
    for (int i = 0; i < BB; i++) c += V - bfs_count(i * N);
    for (int j = 0; j < BB; j++) c += V - bfs_count(BN + j * N);
    return c;
}

/* Simulated annealing over voltages in the current group and base shape.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_cand(double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        for (int t = 0; t < T; t++) sv[t] = -1;
        for (int t = 0; t < T; t++) {
            int g;
            do { g = rndint(N); } while (!free_val(t, g));
            set_v(t, g);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tm = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(T);
            int g;
            do { g = rndint(N); } while (!free_val(t, g));
            int old = sv[t];
            set_v(t, g);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
            } else {
                set_v(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN, BN = BB * N;
    printf("%d %d\n", 2 * BN, T * N);
    for (int t = 0; t < T; t++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", dl[t] * N + g, BN + dr[t] * N + fwd[t][g]);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    int vx = 2 * x->B * x->N, vy = 2 * y->B * y->N;
    if (vx != vy) return vx < vy ? -1 : 1;
    if (x->B != y->B) return x->B - y->B;
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
    int vlo = atoi(argv[5]), vhi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N > MAXN || N < 2 * d) continue;
            for (int B = 1; B <= 2; B++) {
                int V = 2 * B * N;
                if (V < vlo || V > vhi) continue;
                int x0 = (B == 1) ? 0 : 1;
                int xmax = (B == 1) ? 0 : d / 2;
                for (int x = x0; x <= xmax; x++) {
                    if (nc < MAXCAND) {
                        Cand cd = {q, p, k, c, N, B, x};
                        cand[nc++] = cd;
                    }
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending passes over candidates above the current best. Each attempt gets
     * 10% of the remaining time (at least 0.5 s). Later passes retry failed candidates
     * with fresh random starts. */
    int bestV = 0, bestCi = -1;
    int bestSv[MAXT];
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            int V = 2 * cand[ci].B * cand[ci].N;
            if (V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.1 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            Cand cd = cand[ci];
            BB = cd.B;
            setup_group(cd.q, cd.p, cd.k, cd.c);
            set_darts(cd.x);
            if (search_cand(now() + slice)) {
                bestV = V;
                bestCi = ci;
                for (int t = 0; t < T; t++) bestSv[t] = sv[t];
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    Cand cb = cand[bestCi];
    BB = cb.B;
    setup_group(cb.q, cb.p, cb.k, cb.c);
    set_darts(cb.x);
    for (int t = 0; t < T; t++) set_v(t, bestSv[t]);
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

    # Search: group voltage lifts with 1 or 2 base vertices per side over F_q x| H.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        vlo = max(best[0] + 1, mb // 4)
        vhi = mb
        if budget > 2.0 and vlo <= vhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vlo, vhi],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
