"""Multi-orbit voltage lifts over affine and cyclic groups for the bipartite degree-diameter problem.

Construction change: the parent lifts a single base pair of vertices (Haar graphs), so it has
2N vertices for group order N. This version uses a base with K vertices on each side (K = 1, 2, 3)
and a circulant pattern. Left vertex A_i is joined to right vertex B_j by a set S_ij of
M_ij = c[(j - i) mod K] group elements, where c is a composition of d into K positive parts.
Edges are A_i g ~ B_j (g s) for s in S_ij. This is d-regular, bipartite and simple, with 2KN
vertices for group order N.

Left translations are automorphisms, so each class {A_i} and {B_j} is a single orbit. The
diameter test is therefore 2K BFS runs, from A_i e and B_j e. The cost is the total number of
vertices left unreached within distance D, and annealing drives it to 0.

Groups: cyclic Z_N, and affine F_q x| H with H the subgroup of order c in F_q^*, for prime
powers q with N = q*c. Search runs over vertex-count targets in ascending order, and each
attempt gets a share of the remaining time. The result is always checked by lib.is_valid,
with safe fallbacks from the Python constructions and K_{d,d}.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search (K base vertices per side, circulant composition).
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*K*N.
 * Output: "n m" then m lines "u v", or "0 0".
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
#define MAXK 3
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 40000

typedef struct { int K, N, gtype, q, p, kk, c, V; } Cand;

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

/* Multiply field elements a, b (base-p digit vectors) modulo x^k - sum m_i x^i. */
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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;  /* zero divisor: reducible */
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group (cyclic or affine) */

static int GTYPE = 0, GN = 1, GC = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int NEG_ONE_UNUSED;

/* Affine element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(const Cand *cd) {
    GTYPE = cd->gtype;
    if (GTYPE == 0) { GN = cd->N; GC = 1; return; }
    int q = cd->q, c = cd->c;
    build_field(q, cd->p, cd->kk);
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
    if (GTYPE == 0) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    if (GTYPE == 0) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

/* Left vertices A_i g = i*N + g; right vertices B_j h = K*N + j*N + h.
 * Edge A_i g ~ B_j (g s) for s in S_ij, |S_ij| = Mm[i][j]. */
static int K;
static int Mm[MAXK][MAXK];
static int dart[MAXK][MAXK][MAXD], dinv[MAXK][MAXK][MAXD];
static int solD[MAXK][MAXK][MAXD], solMm[MAXK][MAXK];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_dart(int i, int j, int t, int x) {
    dart[i][j][t] = x;
    dinv[i][j][t] = ginv(x);
}

static int in_pair(int i, int j, int x, int upto) {
    for (int t = 0; t < upto; t++)
        if (dart[i][j][t] == x) return 1;
    return 0;
}

static void set_mm(const int *c) {
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            Mm[i][j] = c[((j - i) % K + K) % K];
}

/* Random composition of d into K positive parts (requires d >= K). */
static void rand_comp(int *c) {
    int rem = d;
    for (int t = 0; t < K - 1; t++) {
        int maxv = rem - (K - 1 - t);
        c[t] = 1 + rndint(maxv);
        rem -= c[t];
    }
    c[K - 1] = rem;
}

/* Number of vertices reached from src within distance D. */
static int bfs_reach(int src) {
    int N = GN;
    int KN = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / N, g = v - i * N;
                for (int j = 0; j < K; j++) {
                    int m = Mm[i][j];
                    for (int t = 0; t < m; t++) {
                        int u = KN + j * N + gmul(g, dart[i][j][t]);
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            } else {
                int w = v - KN;
                int j = w / N, h = w - j * N;
                for (int i = 0; i < K; i++) {
                    int m = Mm[i][j];
                    for (int t = 0; t < m; t++) {
                        int u = i * N + gmul(h, dinv[i][j][t]);
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* Left and right classes are each a single orbit under left translation, so one BFS
 * per class decides the diameter. Cost = total unreached (rep, vertex) pairs. */
static long cover_cost(void) {
    long V = 2L * K * GN;
    int KN = K * GN;
    long c = 0;
    for (int i = 0; i < K; i++) c += V - bfs_reach(i * GN);
    for (int j = 0; j < K; j++) c += V - bfs_reach(KN + j * GN);
    return c;
}

static void save_sol(void) {
    memcpy(solD, dart, sizeof dart);
    memcpy(solMm, Mm, sizeof Mm);
}

/* Iterated annealing over compositions and connection sets for the current group.
 * Each round either starts fresh (random composition, random sets) or perturbs the
 * incumbent (two elements replaced). Returns 1 with the valid state saved, 0 on timeout. */
static int search(double until) {
    const int iters = 6000;
    int N = GN;
    int have = 0;
    long bestc = 0;
    static int incD[MAXK][MAXK][MAXD], rD[MAXK][MAXK][MAXD];
    static int incMm[MAXK][MAXK], rMm[MAXK][MAXK];
    while (now() < until) {
        int fresh = !have || rnd01() < 0.4;
        if (fresh) {
            int c[MAXK];
            rand_comp(c);
            set_mm(c);
            for (int i = 0; i < K; i++)
                for (int j = 0; j < K; j++)
                    for (int t = 0; t < Mm[i][j]; t++) {
                        int x;
                        do { x = rndint(N); } while (in_pair(i, j, x, t));
                        set_dart(i, j, t, x);
                    }
        } else {
            memcpy(Mm, incMm, sizeof Mm);
            for (int i = 0; i < K; i++)
                for (int j = 0; j < K; j++)
                    for (int t = 0; t < Mm[i][j]; t++)
                        set_dart(i, j, t, incD[i][j][t]);
            for (int r = 0; r < 2; r++) {
                int i, j;
                do { i = rndint(K); j = rndint(K); } while (Mm[i][j] == 0);
                int t = rndint(Mm[i][j]);
                int x;
                do { x = rndint(N); } while (in_pair(i, j, x, Mm[i][j]));
                set_dart(i, j, t, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) { save_sol(); return 1; }
        double c0 = (double)cost;
        double Ts = (fresh ? 0.05 : 0.02) * c0 + 1.0, Te = 0.3;
        long rbest = cost;
        memcpy(rD, dart, sizeof dart);
        memcpy(rMm, Mm, sizeof Mm);
        for (int it = 0; it < iters; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i, j;
            do { i = rndint(K); j = rndint(K); } while (Mm[i][j] == 0);
            int t = rndint(Mm[i][j]);
            int x;
            do { x = rndint(N); } while (in_pair(i, j, x, Mm[i][j]));
            int old = dart[i][j][t];
            set_dart(i, j, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) { save_sol(); return 1; }
                if (cost < rbest) {
                    rbest = cost;
                    memcpy(rD, dart, sizeof dart);
                    memcpy(rMm, Mm, sizeof Mm);
                }
            } else {
                set_dart(i, j, t, old);
            }
        }
        if (!have || rbest < bestc) {
            have = 1;
            bestc = rbest;
            memcpy(incD, rD, sizeof rD);
            memcpy(incMm, rMm, sizeof rMm);
        }
    }
    return 0;
}

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (lo < 1) lo = 1;
    (void)NEG_ONE_UNUSED;

    static int ppq[MAXQ], ppp[MAXQ], ppk[MAXQ];
    int npp = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, kk;
        if (factor_pp(q, &p, &kk)) {
            ppq[npp] = q; ppp[npp] = p; ppk[npp] = kk; npp++;
        }
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int K0 = 1; K0 <= MAXK && K0 <= d; K0++) {
        long Nlo = (lo + 2L * K0 - 1) / (2L * K0);
        long Nhi = hi / (2L * K0);
        if (Nlo < d) Nlo = d;
        if (Nhi > MAXN) Nhi = MAXN;
        for (long N = Nlo; N <= Nhi; N++) {
            if (nc >= MAXCAND) break;
            Cand cd = {K0, (int)N, 0, 0, 0, 0, 1, (int)(2 * K0 * N)};
            cand[nc++] = cd;
            for (int a = 0; a < npp; a++) {
                int q = ppq[a];
                if (N % q) continue;
                long c = N / q;
                if (c < 1 || c > q - 1 || (q - 1) % c) continue;
                if (nc >= MAXCAND) break;
                Cand e = {K0, (int)N, 1, q, ppp[a], ppk[a], (int)c, (int)(2 * K0 * N)};
                cand[nc++] = e;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);

    /* Ascending by vertex count. A candidate that succeeds immediately costs little,
     * so the sweep climbs quickly through easy orders and spends the time near the
     * threshold. Each attempt gets 20% of the remaining time (at least 1 s). */
    long bestV = 0;
    int have_best = 0;
    Cand bestcfg;
    memset(&bestcfg, 0, sizeof bestcfg);
    for (int ci = 0; ci < nc; ci++) {
        Cand *cd = &cand[ci];
        if (cd->V <= bestV) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        K = cd->K;
        setup_group(cd);
        if (search(now() + slice)) {
            bestV = cd->V;
            bestcfg = *cd;
            have_best = 1;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    K = bestcfg.K;
    setup_group(&bestcfg);
    memcpy(dart, solD, sizeof dart);
    memcpy(Mm, solMm, sizeof Mm);
    int N = GN;
    long n = 2L * K * N, m = (long)K * N * d;
    printf("%ld %ld\n", n, m);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < N; g++)
            for (int j = 0; j < K; j++)
                for (int t = 0; t < Mm[i][j]; t++)
                    printf("%d %d\n", i * N + g, K * N + j * N + gmul(g, dart[i][j][t]));
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

    # Search: multi-orbit lifts (K = 1, 2, 3 base vertices per side) over cyclic and
    # affine groups, with the total vertex count swept upward from a lower bound.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 5)
        hi = mb // 2
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
