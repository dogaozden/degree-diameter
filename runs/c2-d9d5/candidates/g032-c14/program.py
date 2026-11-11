"""Two-class voltage lifts with a search fallback for the bipartite degree-diameter problem.

This version adds a construction family the parent did not search. Take an a x a base
bipartite multigraph (a = 1 or 2 classes per side) with multiplicity matrix M. For a = 2,
M = [[x, d-x], [d-x, x]]; for a = 1, M = [[d]]. Lift it over a group G = F_q x| H (order
N = q*c) with distinct voltages inside each base pair. The lift has 2aN vertices, is
d-regular and bipartite, and is simple. Left translations are automorphisms that act
regularly on each class, so the diameter check needs only 2a BFS runs, one per class
representative. The C engine runs simulated annealing over the voltages, with candidates
sorted by order and retried in passes. Python keeps valid fallbacks and validates the
result.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Voltage-lift search over affine groups, with 1- or 2-class bases.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*a*N.
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
#define MAXN 4096
#define MAXD 32
#define MAXE (2 * MAXD)
#define MAXV (4 * MAXN)
#define MAXCAND 40000

typedef struct { int q, p, k, c, N, a, x; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
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

/* Base: A classes per side. Darts e = 0..E-1 join left class dL[e] to right class dR[e]
 * with voltage vol[e]. Left (i,g) ~ right (j, g*s); right (j,h) ~ left (i, h*s^-1).
 * Vertex id: class cl (0..A-1 left, A..2A-1 right) times N plus group index. */
static int A, E;
static int dL[MAXE], dR[MAXE];
static int Lidx[2][MAXD], Ridx[2][MAXD];
static int vol[MAXE], vinv[MAXE];
static int FW[MAXE][MAXN], BW[MAXE][MAXN];
static unsigned int vis[MAXV];
static unsigned int stamp_ = 0;
static int que[MAXV];
static int bestvol[MAXE];

static void build_structure(int a, int x) {
    int M[2][2] = {{0, 0}, {0, 0}};
    A = a;
    if (a == 1) {
        M[0][0] = d;
    } else {
        M[0][0] = x;
        M[0][1] = d - x;
        M[1][0] = d - x;
        M[1][1] = x;
    }
    E = 0;
    for (int i = 0; i < a; i++)
        for (int j = 0; j < a; j++)
            for (int t = 0; t < M[i][j]; t++) {
                dL[E] = i;
                dR[E] = j;
                E++;
            }
    for (int i = 0; i < a; i++) {
        int k = 0;
        for (int e = 0; e < E; e++)
            if (dL[e] == i) Lidx[i][k++] = e;
    }
    for (int j = 0; j < a; j++) {
        int k = 0;
        for (int e = 0; e < E; e++)
            if (dR[e] == j) Ridx[j][k++] = e;
    }
}

static void set_vol(int e, int s) {
    vol[e] = s;
    vinv[e] = ginv(s);
    for (int g = 0; g < GN; g++) {
        FW[e][g] = gmul(g, s);
        BW[e][g] = gmul(g, vinv[e]);
    }
}

static void setup_cand(const Cand *cd) {
    setup_group(cd->q, cd->p, cd->k, cd->c);
    build_structure(cd->a, cd->x);
    for (int e = 0; e < E; e++) vol[e] = -1;
}

/* Parallel edges forbidden: darts in the same base pair need distinct voltages. */
static int conflict(int e, int s) {
    for (int f = 0; f < E; f++)
        if (f != e && vol[f] == s && dL[f] == dL[e] && dR[f] == dR[e]) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN;
    if (++stamp_ == 0) {
        memset(vis, 0, sizeof(vis));
        stamp_ = 1;
    }
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int cl = v / N, g = v - cl * N;
            if (cl < A) {
                for (int k = 0; k < d; k++) {
                    int e = Lidx[cl][k];
                    int u = (A + dR[e]) * N + FW[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = cl - A;
                for (int k = 0; k < d; k++) {
                    int e = Ridx[j][k];
                    int u = dL[e] * N + BW[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms acting regularly on each class, so one BFS per
 * class representative (identity element) decides the diameter. */
static long cover_cost(void) {
    int V = 2 * A * GN;
    long cost = 0;
    for (int cl = 0; cl < 2 * A; cl++)
        cost += (long)(V - bfs_count(cl * GN));
    return cost;
}

/* Simulated annealing over the voltages of the current candidate.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_cfg(double until) {
    const int iters = 6000;
    while (now() < until) {
        for (int e = 0; e < E; e++) vol[e] = -1;
        for (int e = 0; e < E; e++) {
            int s, tries = 0;
            do {
                s = rndint(GN);
                tries++;
            } while (conflict(e, s) && tries < 10000);
            set_vol(e, s);
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(E);
            int s = -1;
            for (int tr = 0; tr < 50; tr++) {
                int cs = rndint(GN);
                if (cs != vol[e] && !conflict(e, cs)) { s = cs; break; }
            }
            if (s < 0) continue;
            int old = vol[e];
            set_vol(e, s);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_vol(e, old);
            }
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * A * N, A * N * d);
    for (int i = 0; i < A; i++)
        for (int g = 0; g < N; g++)
            for (int k = 0; k < d; k++) {
                int e = Lidx[i][k];
                printf("%d %d\n", i * N + g, (A + dR[e]) * N + FW[e][g]);
            }
}

static int cvert(const Cand *c) { return 2 * c->a * c->N; }

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
    if (lo < 1) lo = 1;
    if (hi > MAXV) hi = MAXV;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N > MAXN || N < 2 * d) continue;
            if (2 * N >= lo && 2 * N <= hi && nc < MAXCAND) {
                Cand cd = {q, p, k, c, N, 1, d};
                cand[nc++] = cd;
            }
            if (4 * N >= lo && 4 * N <= hi) {
                for (int x = 1; 2 * x <= d; x++)
                    if (nc < MAXCAND) {
                        Cand cd = {q, p, k, c, N, 2, x};
                        cand[nc++] = cd;
                    }
            }
        }
    }
    /* Insertion sort by total vertex count, ascending. */
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cvert(&cand[j]) > cvert(&t)) {
            cand[j + 1] = cand[j];
            j--;
        }
        cand[j + 1] = t;
    }

    /* Repeated passes in ascending order. Each attempt gets 25% of the remaining
     * time, clamped to [0.6, 4] s. Failed candidates are retried in later passes. */
    int bestV = 0, bestIdx = -1;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            int V = cvert(&cand[ci]);
            if (V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.2) break;
            tried = 1;
            double slice = 0.25 * rem;
            if (slice < 0.6) slice = 0.6;
            if (slice > 4.0) slice = 4.0;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_cfg(now() + slice)) {
                bestV = V;
                bestIdx = ci;
                memcpy(bestvol, vol, sizeof(int) * (size_t)E);
            }
        }
        if (!tried || t_end - now() < 0.2) break;
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&cand[bestIdx]);
    for (int e = 0; e < E; e++) set_vol(e, bestvol[e]);
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

    # Search: one C run over both 1-class (Haar) and 2-class lifts, ascending in order.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8)
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
