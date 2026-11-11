"""Two-orbit voltage lifts over cyclic and affine groups for the bipartite degree-diameter problem.

Idea: the parent searched only one-orbit Haar lifts, which are lifts of a
2-vertex base with d parallel darts. This version also searches 4-vertex base
graphs with count matrix [[a, d-a], [d-a, a]] and 1 <= a <= d-1. Each dart
(i, j, s) joins L_{i,g} to R_{j,g*s}. Vertex count is 2*M*N for M in {1, 2}.
Groups are cyclic Z_N or affine F_q x| H. Left translations are automorphisms,
so the diameter test needs only BFS from the 2M base vertices (L_{i,e} and R_{j,e}).

Search: candidates are sorted by total order and tried in ascending order, each
with a time slice, and retried in later passes. Simulated annealing over dart
values keeps each dart's group element distinct within its pair class.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit voltage lift search over cyclic and affine groups.
 * Usage: prog d D seed time_limit lo hi   (stdin ignored)
 * lo, hi bound the TOTAL vertex count 2*M*N.
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
#define MAXN 8192
#define MAXD 32
#define MAXM 2
#define MAXDART (MAXM * MAXD)
#define MAXV (2 * MAXM * MAXN)
#define MAXCAND 20000

typedef struct { int M, type, q, p, k, c, N, V; } Cand;

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

/* ------------------------------------------------------------ group */

/* gtype 0: cyclic Z_GN. gtype 1: affine F_q x| H, element (a, h_j) coded a*GC + j. */
static int gtype = 1;
static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 1;
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
    gtype = 0;
    GQ = 0;
    GC = 1;
    GN = N;
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int r = x + y;
        return r >= GN ? r - GN : r;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    if (gtype == 0) return x == 0 ? 0 : GN - x;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

/* Vertices: L_{i,g} = i*GN + g (i < M); R_{j,h} = M*GN + j*GN + h.
 * Dart t = (dI[t], dJ[t], dS[t]) joins L_{i,g} to R_{j, g*s}.
 * Pair p = i*M + j has cntP[p] darts; darts of a pair are contiguous at offP[p]. */
static int M, nd;
static int cntP[4], offP[4];
static int dI[MAXDART], dJ[MAXDART], dP[MAXDART];
static int dS[MAXDART], dSinv[MAXDART];
static int fwdT[MAXDART][MAXN], bwdT[MAXDART][MAXN];
static int Ldarts[MAXM][MAXD], Rdarts[MAXM][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void build_structure(void) {
    nd = 0;
    for (int p = 0; p < M * M; p++) {
        offP[p] = nd;
        for (int k = 0; k < cntP[p]; k++) {
            dI[nd] = p / M;
            dJ[nd] = p % M;
            dP[nd] = p;
            nd++;
        }
    }
    for (int i = 0; i < M; i++) {
        int lc = 0;
        for (int t = 0; t < nd; t++)
            if (dI[t] == i && lc < MAXD) Ldarts[i][lc++] = t;
    }
    for (int j = 0; j < M; j++) {
        int rc = 0;
        for (int t = 0; t < nd; t++)
            if (dJ[t] == j && rc < MAXD) Rdarts[j][rc++] = t;
    }
}

static void set_counts(int a) {
    if (M == 1) {
        cntP[0] = d;
    } else {
        cntP[0] = a;
        cntP[1] = d - a;
        cntP[2] = d - a;
        cntP[3] = a;
    }
    build_structure();
}

static void refresh(int t) {
    int x = dS[t];
    int xi = ginv(x);
    dSinv[t] = xi;
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        bwdT[t][g] = gmul(g, xi);
    }
}

static void random_config(void) {
    int a = (M == 2) ? 1 + rndint(d - 1) : d;
    set_counts(a);
    for (int p = 0; p < M * M; p++) {
        for (int k = 0; k < cntP[p]; k++) {
            int t = offP[p] + k;
            int x, ok;
            do {
                x = rndint(GN);
                ok = 1;
                for (int u = offP[p]; u < t; u++)
                    if (dS[u] == x) { ok = 0; break; }
            } while (!ok);
            dS[t] = x;
            refresh(t);
        }
    }
}

/* BFS from src (vertex index); returns the number of vertices within distance D. */
static int bfs_count(int src) {
    int MN = M * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < MN) {
                int i = v / GN, g = v - i * GN;
                for (int k = 0; k < d; k++) {
                    int t = Ldarts[i][k];
                    int u = MN + dJ[t] * GN + fwdT[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - MN;
                int j = w / GN, h = w - j * GN;
                for (int k = 0; k < d; k++) {
                    int t = Rdarts[j][k];
                    int u = dI[t] * GN + bwdT[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms, so BFS from L_{i,e} and R_{j,e} decides the diameter. */
static long cover_cost(void) {
    int MN = M * GN;
    int V = 2 * MN;
    long c = 0;
    for (int i = 0; i < M; i++) c += (long)(V - bfs_count(i * GN));
    for (int j = 0; j < M; j++) c += (long)(V - bfs_count(MN + j * GN));
    return c;
}

/* Simulated annealing over dart values. Returns 1 at cost 0, 0 on timeout. */
static int search_cfg(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_config();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(nd);
            int p = dP[t];
            int g0 = offP[p], g1 = offP[p] + cntP[p];
            int x, ok;
            do {
                x = rndint(GN);
                ok = (x != dS[t]);
                for (int u = g0; ok && u < g1; u++)
                    if (u != t && dS[u] == x) ok = 0;
            } while (!ok);
            int old = dS[t];
            dS[t] = x;
            refresh(t);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                dS[t] = old;
                refresh(t);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int MN = M * GN;
    printf("%d %d\n", 2 * MN, MN * d);
    for (int i = 0; i < M; i++)
        for (int g = 0; g < GN; g++)
            for (int k = 0; k < d; k++) {
                int t = Ldarts[i][k];
                printf("%d %d\n", i * GN + g, MN + dJ[t] * GN + fwdT[t][g]);
            }
}

static void setup_cand(const Cand *c) {
    M = c->M;
    if (c->type == 0) setup_cyclic(c->N);
    else setup_affine(c->q, c->p, c->k, c->c);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->V > y->V) - (x->V < y->V);
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

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int Mm = 1; Mm <= MAXM; Mm++) {
        for (long N = 2L * d; N <= MAXN; N++) {
            long V = 2L * Mm * N;
            if (V < lo || V > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].M = Mm;
                cand[nc].type = 0;
                cand[nc].q = cand[nc].p = cand[nc].k = cand[nc].c = 0;
                cand[nc].N = (int)N;
                cand[nc].V = (int)V;
                nc++;
            }
        }
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 2; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                if (N < 2L * d || N > MAXN) continue;
                long V = 2L * Mm * N;
                if (V < lo || V > hi) continue;
                if (nc < MAXCAND) {
                    cand[nc].M = Mm;
                    cand[nc].type = 1;
                    cand[nc].q = q;
                    cand[nc].p = p;
                    cand[nc].k = k;
                    cand[nc].c = c;
                    cand[nc].N = (int)N;
                    cand[nc].V = (int)V;
                    nc++;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending passes. Each attempt gets 20% of the remaining time (at least 1 s).
     * Failed candidates are retried in later passes with fresh random starts. */
    int bestV = 0, bestci = -1, bestM = 1;
    int bestCnt[4];
    int bestDS[MAXDART];
    memset(bestCnt, 0, sizeof bestCnt);
    memset(bestDS, 0, sizeof bestDS);
    for (int pass = 0; pass < 1000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.2 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_cfg(now() + slice)) {
                bestV = cand[ci].V;
                bestci = ci;
                bestM = M;
                memcpy(bestCnt, cntP, sizeof cntP);
                memcpy(bestDS, dS, sizeof(int) * (size_t)nd);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (bestci < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&cand[bestci]);
    M = bestM;
    memcpy(cntP, bestCnt, sizeof cntP);
    build_structure();
    memcpy(dS, bestDS, sizeof(int) * (size_t)nd);
    for (int t = 0; t < nd; t++) refresh(t);
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

    # Search over one-orbit and two-orbit voltage lifts; the range is in total vertices.
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
