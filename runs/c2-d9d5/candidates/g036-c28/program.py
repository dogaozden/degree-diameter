"""Two-class bi-Cayley lift search for the bipartite degree-diameter problem.

Change in this version: the parent searched one Haar graph on an affine group G,
with 2|G| vertices. This version searches a base graph with K = 2 left and K = 2
right vertices. Each base vertex is lifted over G, so the graph has 4|G| vertices.
Left and right translations are automorphisms, so the diameter check only needs
BFS from the identity of each of the 2K fibres. The darts form a 2x2 pattern
[[t, d-t], [d-t, t]], which keeps every degree equal to d. Each dart carries a
voltage in G, and voltages on the same base edge are kept distinct, so the graph
is simple. Simulated annealing over the voltages minimises the number of
vertices not reached within D from the 2K roots.

Search order: ascending group orders from the smallest admissible one above the
current best, with a per-order slice of the remaining time and a cap on
consecutive failures. If K = 2 finds nothing, the program falls back to the
K = 1 (Haar) family, which contains the parent's construction. Python keeps the
projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d} fallback. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base group-lift search.
 * Usage: prog d D seed time_limit lo_total hi_total
 * Vertices: left (u,x) = u*N+x, right (v,y) = K*N + v*N+y, for u,v < K.
 * Dart j from left u to right v with voltage a: (u,x) ~ (v, x*a).
 * Output: "n m" then m lines "u v" for the best valid graph, or "0 0".
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
#define MAXM 64
#define MAXV (2 * 2 * MAXN)
#define MAXCAND 4096

typedef struct { int type, q, p, k, c, N; } Cand;   /* type 0 affine, 1 cyclic */

typedef struct {
    int total, K, t;
    Cand cd;
    int avol[MAXM];
} Result;

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

/* ------------------------------------------------------------ group G */

static int GTYPE = 0, GN = 0, GQ = 0, GC = 0;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Affine group F_q x| H, H the subgroup of order c. Element (a, h_j) is coded a*c+j. */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GTYPE = 0;
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

static void setup_cyclic(int N) {
    GTYPE = 1;
    GN = N;
    GQ = 0;
    GC = 0;
}

static inline int gmul(int x, int y) {
    if (GTYPE == 1) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    if (GTYPE == 1) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_affine(cd->q, cd->p, cd->k, cd->c);
    else setup_cyclic(cd->N);
}

/* ------------------------------------------------------------ lift state */

static int K, M, T_PAT;
static int dsrc[MAXM], ddst[MAXM];
static int avol[MAXM];
static int fwdv[MAXM][MAXN], bwdv[MAXM][MAXN];
static int ldart[2][MAXD], rdart[2][MAXD];

/* K = 1: d darts from left 0 to right 0 (Haar graph).
 * K = 2: class counts [[t, d-t], [d-t, t]], so every base vertex has degree d. */
static void build_pattern(int t) {
    T_PAT = t;
    if (K == 1) {
        M = d;
        for (int j = 0; j < d; j++) { dsrc[j] = 0; ddst[j] = 0; }
    } else {
        int c[2][2] = {{t, d - t}, {d - t, t}};
        M = 0;
        for (int u = 0; u < 2; u++)
            for (int v = 0; v < 2; v++)
                for (int r = 0; r < c[u][v]; r++) {
                    dsrc[M] = u;
                    ddst[M] = v;
                    M++;
                }
    }
    int lc[2] = {0, 0}, rc[2] = {0, 0};
    for (int j = 0; j < M; j++) {
        ldart[dsrc[j]][lc[dsrc[j]]++] = j;
        rdart[ddst[j]][rc[ddst[j]]++] = j;
    }
}

static void set_volt(int j, int x) {
    avol[j] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdv[j][g] = gmul(g, x);
        bwdv[j][g] = gmul(g, xi);
    }
}

/* True if voltage x on dart j clashes with an earlier dart (i < lim) on the same base edge. */
static int conflict(int j, int x, int lim) {
    for (int i = 0; i < lim; i++)
        if (i != j && dsrc[i] == dsrc[j] && ddst[i] == ddst[j] && avol[i] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------ BFS and cost */

static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int reach_count(int root) {
    int base_r = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = root;
    vis[root] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < base_r) {
                int u = v / GN, x = v - u * GN;
                for (int i = 0; i < d; i++) {
                    int j = ldart[u][i];
                    int w = base_r + ddst[j] * GN + fwdv[j][x];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            } else {
                int r = v - base_r;
                int vv = r / GN, y = r - vv * GN;
                for (int i = 0; i < d; i++) {
                    int j = rdart[vv][i];
                    int w = dsrc[j] * GN + bwdv[j][y];
                    if (vis[w] != stamp_) { vis[w] = stamp_; que[tail++] = w; }
                }
            }
        }
    }
    return tail;
}

/* Left and right translations act transitively on each fibre, so the roots are
 * the identities of the 2K fibres. Cost = total vertices not reached within D. */
static long cover_cost(void) {
    long V = 2L * K * GN, c = 0;
    for (int u = 0; u < K; u++) {
        c += V - reach_count(u * GN);
        c += V - reach_count(K * GN + u * GN);
    }
    return c;
}

/* Simulated annealing over the base pattern and voltages.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
static int search_group(double until) {
    while (now() < until) {
        int t = (K == 2) ? 1 + rndint(d - 1) : 0;
        build_pattern(t);
        for (int j = 0; j < M; j++) {
            int x;
            do { x = rndint(GN); } while (conflict(j, x, j));
            set_volt(j, x);
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.1 * c0 + 1.0, Te = 0.2;
        const int iters = 6000;
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int j = rndint(M);
            int x;
            do { x = rndint(GN); } while (conflict(j, x, M));
            int old = avol[j];
            set_volt(j, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_volt(j, old);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ phases */

static Result best;
static int have_best = 0;

static void run_phase(int Kv, int lo_total, int hi_total, double until, int maxfail) {
    K = Kv;
    long Nlo = (lo_total + 2L * Kv - 1) / (2L * Kv);
    long Nhi = hi_total / (2L * Kv);
    if (Nhi > MAXN) Nhi = MAXN;
    if (Nlo < 2L * d) Nlo = 2L * d;
    if (Nlo > Nhi) return;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < Nlo || N > Nhi) continue;
            if (nc < MAXCAND) {
                Cand cd = {0, q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    if (nc == 0) {
        for (long N = Nlo; N <= Nhi && nc < MAXCAND; N++) {
            Cand cd = {1, 0, 0, 0, 0, (int)N};
            cand[nc++] = cd;
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int fails = 0;
    for (int ci = 0; ci < nc && now() < until && fails < maxfail; ci++) {
        Cand cd = cand[ci];
        if (have_best && 2L * Kv * cd.N <= best.total) continue;
        double rem = until - now();
        double slice = rem * 0.25;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        setup_cand(&cd);
        if (search_group(now() + slice)) {
            best.total = 2 * Kv * GN;
            best.K = Kv;
            best.t = T_PAT;
            best.cd = cd;
            for (int j = 0; j < M; j++) best.avol[j] = avol[j];
            have_best = 1;
            fails = 0;
        } else {
            fails++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo_total = atoi(argv[5]), hi_total = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo_total < 1) lo_total = 1;

    run_phase(2, lo_total, hi_total, t_end, 4);
    if (now() < t_end - 3.0) {
        int lo1 = have_best ? best.total + 1 : lo_total;
        run_phase(1, lo1, hi_total, t_end, 4);
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }

    K = best.K;
    setup_cand(&best.cd);
    build_pattern(best.t);
    for (int j = 0; j < M; j++) set_volt(j, best.avol[j]);
    int N = GN;
    int V = 2 * K * N;
    long E = (long)K * N * d;
    printf("%d %ld\n", V, E);
    for (int u = 0; u < K; u++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int j = ldart[u][i];
                printf("%d %d\n", u * N + x, K * N + ddst[j] * N + fwdv[j][x]);
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

    # Two-class bi-Cayley lift search. Total order is 2K|G| with K in {1, 2}.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 4.0
        lo = best[0] + 1
        if budget > 3.0 and lo <= mb:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, mb],
                                 stdin_graph=None, timeout=budget + 6.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
