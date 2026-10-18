"""Bi-Cayley lifts with two base orbits per side for the bipartite degree-diameter problem.

The parent searched one-orbit Haar graphs over F_q x| H. This version adds a second
construction family: a base graph with K in {1, 2} vertices per side, K*d darts in total,
and a circulant dart-count matrix (c_t darts from left i to right i+t mod K, sum c_t = d).
Each dart carries a voltage in the group G = F_q x| H. Vertex (f, g) with f < K is a left
vertex and f >= K is a right vertex. Left multiplication by G acts on each fiber, so the
diameter test needs one BFS per fiber representative, 2K BFS runs in total.

K = 1 reproduces the parent's Haar family. K = 2 gives 4N vertices for group order N, a
different order set that the one-orbit family cannot reach. Candidates are ordered by
vertex count, starting above the Python fallback, and each is annealed from the incumbent
(iterated annealing as in the parent). Python validates everything, and K_{d,d} or the
projective/Araujo-Lopez constructions remain the fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over G = F_q x| H with K in {1,2} base vertices per side.
 * Usage: prog d D seed time_limit lo_v hi_v      (stdin ignored)
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
#define MAXN 4800
#define MAXV 9800
#define MAXD 32
#define MAXE 64
#define MAXCAND 20000

typedef struct { int q, p, kf, c, N, k, a, V; } Cand;

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

static int factor_pp(int q, int *p, int *kf) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *kf = kk;
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

static void build_field(int q, int p, int kf) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= kf; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < kf; i++)
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
        for (int i = 0; i < kf; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, kf, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, kf, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int kf, int c) {
    build_field(q, p, kf);
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

/* ------------------------------------------------------------ bi-Cayley state */

/* K base vertices per side. Darts e: left fiber dfrom[e] -> right fiber dto[e], voltage dsv[e].
 * Left vertex (i,g) = i*NN+g. Right vertex (j,h) = (K+j)*NN+h.
 * Edges: (i,g) ~ (K+dto[e], g * s_e), so right (j,h) ~ (dfrom[e], h * s_e^-1).
 * Darts in the same block (i, t) have pairwise distinct voltages, so the graph is simple. */
static int K, NN, ND;
static int ct[2];
static int dfrom[MAXE], dto[MAXE], dblk[MAXE], dsv[MAXE];
static int ldart[2][MAXD], rdart[2][MAXD];
static int fwd[MAXE][MAXN], bwd[MAXE][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestVolt[MAXE];
static Cand bestCand;

static void set_dart(int e, int x) {
    dsv[e] = x;
    int ix = ginv(x);
    for (int g = 0; g < NN; g++) {
        fwd[e][g] = gmul(g, x);
        bwd[e][g] = gmul(g, ix);
    }
}

static void build_cfg(const Cand *cd) {
    setup_group(cd->q, cd->p, cd->kf, cd->c);
    K = cd->k;
    NN = GN;
    ND = K * d;
    if (K == 1) {
        ct[0] = d;
        ct[1] = 0;
    } else {
        ct[0] = cd->a;
        ct[1] = d - cd->a;
    }
    int lc[2] = {0, 0}, rc[2] = {0, 0};
    int e = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < K; t++)
            for (int r = 0; r < ct[t]; r++) {
                dfrom[e] = i;
                dto[e] = (i + t) % K;
                dblk[e] = i * K + t;
                e++;
            }
    for (int e2 = 0; e2 < ND; e2++) {
        int i = dfrom[e2], j = dto[e2];
        ldart[i][lc[i]++] = e2;
        rdart[j][rc[j]++] = e2;
    }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int f = v / NN, g = v - f * NN;
            if (f < K) {
                for (int r = 0; r < d; r++) {
                    int e = ldart[f][r];
                    int u = (K + dto[e]) * NN + fwd[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = f - K;
                for (int r = 0; r < d; r++) {
                    int e = rdart[j][r];
                    int u = dfrom[e] * NN + bwd[e][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left multiplication acts transitively on each fiber, so one BFS per fiber
 * representative decides diameter <= D. */
static long cover_cost(void) {
    long V = 2L * K * NN;
    long c = 0;
    for (int f = 0; f < 2 * K; f++) c += V - bfs_count(f * NN);
    return c;
}

/* 1 if voltage x is already used by a dart e2 < upto (e2 != e) in the same block as e. */
static int conflict(int e, int x, int upto) {
    for (int e2 = 0; e2 < upto; e2++)
        if (e2 != e && dblk[e2] == dblk[e] && dsv[e2] == x) return 1;
    return 0;
}

/* Iterated annealing over the voltages. The first round starts from random voltages;
 * later rounds start from the incumbent with two darts re-drawn, at a lower temperature.
 * Returns 1 when cost 0 is reached (state left in dsv), 0 on timeout. */
static int search_cfg(double until) {
    const int iters = 6000;
    int have = 0;
    long bestc = 0;
    int inc[MAXE];
    while (now() < until) {
        if (!have) {
            for (int e = 0; e < ND; e++) {
                int x;
                do { x = rndint(NN); } while (conflict(e, x, e));
                set_dart(e, x);
            }
        } else {
            for (int e = 0; e < ND; e++) set_dart(e, inc[e]);
            for (int t = 0; t < 2; t++) {
                int e = rndint(ND), x;
                do { x = rndint(NN); } while (conflict(e, x, ND));
                set_dart(e, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int e = rndint(ND), x;
            do { x = rndint(NN); } while (conflict(e, x, ND));
            int old = dsv[e];
            set_dart(e, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(e, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(inc, dsv, sizeof(int) * (size_t)ND);
        }
    }
    return 0;
}

static void print_result(void) {
    long V = 2L * K * NN;
    long E = (long)K * NN * d;
    printf("%ld %ld\n", V, E);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < NN; g++)
            for (int r = 0; r < d; r++) {
                int e = ldart[i][r];
                printf("%d %d\n", i * NN + g, (K + dto[e]) * NN + fwd[e][g]);
            }
}

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->V != b->V) return a->V < b->V ? -1 : 1;
    int sa = abs(2 * a->a - d), sb = abs(2 * b->a - d);
    return sa - sb;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXV) hi = MAXV;
    if (lo < 1) lo = 1;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int k = 1; k <= 2; k++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, kf;
            if (!factor_pp(q, &p, &kf)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                long V = 2L * k * N;
                if (N > MAXN || V > MAXV || V < lo || V > hi) continue;
                if (k == 1) {
                    if (nc < MAXCAND) {
                        Cand cd = {q, p, kf, c, (int)N, 1, d, (int)V};
                        cand[nc++] = cd;
                    }
                } else {
                    for (int a = 1; a <= d - 1; a++) {
                        if (nc < MAXCAND) {
                            Cand cd = {q, p, kf, c, (int)N, 2, a, (int)V};
                            cand[nc++] = cd;
                        }
                    }
                }
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending order by vertex count from lo: each attempt gets 20% of the remaining
     * time (at least 1 s). Candidates not above the current best are skipped. */
    int bestV = 0, bestIdx = -1;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].V <= bestV) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        build_cfg(&cand[ci]);
        if (search_cfg(now() + slice)) {
            bestV = cand[ci].V;
            bestIdx = ci;
            bestCand = cand[ci];
            memcpy(bestVolt, dsv, sizeof(int) * (size_t)ND);
        }
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    build_cfg(&bestCand);
    for (int e = 0; e < ND; e++) set_dart(e, bestVolt[e]);
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

    # Search: bi-Cayley lifts (K = 1 or 2 base vertices per side) over F_q x| H.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
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
