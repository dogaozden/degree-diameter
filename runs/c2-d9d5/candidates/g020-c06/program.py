"""Multi-base group lifts for the bipartite degree-diameter problem.

Change in this version: the parent searched only single-base lifts (Haar graphs
over affine groups). This version searches B-base lifts. A B-base lift has 2B
fibres of size N = |G|, one left and one right fibre per base vertex. Each left
fibre has d darts, each right fibre has d darts, and dart (i, j, g) joins
(i, x) to (j, x*g) for all x. The base multiplicities form a circulant pattern
mv[o] (o = (j - i) mod B) with sum d, chosen at random per restart. The darts
carry group elements that are distinct within each (i, o) block, so the graph is
simple and d-regular. Left translations act transitively on each fibre, so
diameter <= D reduces to BFS runs from one vertex per fibre (2B BFS runs).

The C engine searches cyclic groups Z_m and affine groups F_q x| H over B in 1..4,
using a binary search over the sorted candidate orders with equal time slices,
then a short upward scan. Python keeps the projective-plane, Araujo-Lopez,
W(q) and K_{d,d} constructions as fallbacks, and every returned graph is checked
with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base group lift search.
 * Usage: prog d D seed time_limit loT hiT    (stdin ignored)
 * Finds a valid graph with total order T in (loT, hiT] if possible.
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
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
#define MAXB 4
#define MAXDART (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 40000

typedef struct { int type, q, p, k, c, N, B, T; } Cand;

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

/* gtype 0: cyclic Z_GN.  gtype 1: affine F_q x| H, element (a, h_j) coded a*GC + j. */
static int gtype = 0, GN = 1, GC = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 1;
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
    if (gtype == 0) {
        int s = x + y;
        return s >= GN ? s - GN : s;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    if (gtype == 0) return x ? GN - x : 0;
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ multi-base lift state */

static int B = 1, BN = 1, V = 2;
static int mv[MAXB];
static int offT[MAXD];
static int NDART = 0;
static int lc[MAXB], rc[MAXB];
static int dfrom[MAXDART], dto[MAXDART], dg[MAXDART];
static int lbase[MAXB][MAXD], rbase[MAXB][MAXD];
static int fwdg[MAXDART][MAXN], bwdg[MAXDART][MAXN];
static int bestdg[MAXDART], bestmv[MAXB];

/* Vertices: left (i, x) = i*GN + x; right (j, y) = BN + j*GN + y.
 * Dart k from left fibre i to right fibre j with group element g maps
 * (i, x) to (j, x*g); its inverse maps (j, y) back to (i, y*g^-1). */

static void random_mv(void) {
    for (int o = 0; o < B; o++) mv[o] = 0;
    for (int c = 0; c < d; c++) mv[rndint(B)]++;
}

static void layout(void) {
    int t = 0;
    for (int o = 0; o < B; o++)
        for (int c = 0; c < mv[o]; c++) offT[t++] = o;
    NDART = B * d;
    for (int i = 0; i < B; i++) { lc[i] = 0; rc[i] = 0; }
    for (int i = 0; i < B; i++)
        for (int t2 = 0; t2 < d; t2++) {
            int k = i * d + t2;
            dfrom[k] = i;
            dto[k] = (i + offT[t2]) % B;
            lbase[i][lc[i]++] = k;
            rbase[dto[k]][rc[dto[k]]++] = k;
        }
}

static void rebuild_dart(int k) {
    int gi = ginv(dg[k]);
    int g = dg[k];
    for (int x = 0; x < GN; x++) {
        fwdg[k][x] = gmul(x, g);
        bwdg[k][x] = gmul(x, gi);
    }
}

/* True if g is already used by another dart in the same block (same left fibre, same offset). */
static int conflicts(int k, int g) {
    int i = dfrom[k], t = k % d;
    for (int t2 = 0; t2 < d; t2++) {
        if (t2 == t || offT[t2] != offT[t]) continue;
        if (dg[i * d + t2] == g) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ cost */

static int vis[MAXV], que[MAXV];
static int stamp = 0;

static int bfs_count(int src) {
    if (stamp > 1000000000) { memset(vis, 0, sizeof(vis)); stamp = 0; }
    stamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / GN, x = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int k = lbase[i][t];
                    int u = BN + dto[k] * GN + fwdg[k][x];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / GN, y = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int k = rbase[j][t];
                    int u = dfrom[k] * GN + bwdg[k][y];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Fibre transitivity: BFS from (i, e) for every left fibre i and (j, e) for every right fibre j. */
static long cover_cost(void) {
    long c = 0;
    for (int i = 0; i < B; i++) {
        c += (long)(V - bfs_count(i * GN));
        c += (long)(V - bfs_count(BN + i * GN));
    }
    return c;
}

/* ------------------------------------------------------------ search */

static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_mv();
        layout();
        int ND = NDART;
        for (int k = 0; k < ND; k++) dg[k] = -1;
        for (int k = 0; k < ND; k++) {
            int g;
            do { g = rndint(GN); } while (conflicts(k, g));
            dg[k] = g;
        }
        for (int k = 0; k < ND; k++) rebuild_dart(k);

        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(ND);
            int g;
            do { g = rndint(GN); } while (g == dg[k] || conflicts(k, g));
            int old = dg[k];
            dg[k] = g;
            rebuild_dart(k);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                dg[k] = old;
                rebuild_dart(k);
            }
        }
        if (cost == 0) {
            memcpy(bestdg, dg, sizeof(int) * (size_t)ND);
            memcpy(bestmv, mv, sizeof(int) * (size_t)B);
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void apply_cand(const Cand *cd) {
    B = cd->B;
    if (cd->type == 0) {
        gtype = 0;
        GN = cd->N;
        GC = 1;
    } else {
        setup_affine(cd->q, cd->p, cd->k, cd->c);
    }
    BN = B * GN;
    V = 2 * BN;
}

static int probe(int idx, double until) {
    apply_cand(&cand[idx]);
    return search_group(until);
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->T != y->T) return x->T < y->T ? -1 : 1;
    return x->N - y->N;
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
    long loT = atol(argv[5]), hiT = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }
    if (loT < 0) loT = 0;
    if (hiT > MAXV) hiT = MAXV;

    /* Cyclic candidates: N = m, total order T = 2*B*m. */
    for (int Bb = 1; Bb <= MAXB; Bb++) {
        long mlo = loT / (2L * Bb) + 1;
        if (mlo < d + 1) mlo = d + 1;
        long mhi = hiT / (2L * Bb);
        if (mhi > MAXN) mhi = MAXN;
        for (long m = mlo; m <= mhi && nc < MAXCAND; m++) {
            Cand cd;
            cd.type = 0; cd.q = 0; cd.p = 0; cd.k = 0; cd.c = 1;
            cd.N = (int)m; cd.B = Bb; cd.T = (int)(2L * Bb * m);
            cand[nc++] = cd;
        }
    }
    /* Affine candidates: N = q*c with c | q-1, N > d. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N > MAXN || N <= d) continue;
            for (int Bb = 1; Bb <= MAXB; Bb++) {
                long T = 2L * Bb * N;
                if (T <= loT || T > hiT) continue;
                if (nc >= MAXCAND) break;
                Cand cd;
                cd.type = 1; cd.q = q; cd.p = p; cd.k = k; cd.c = c;
                cd.N = (int)N; cd.B = Bb; cd.T = (int)T;
                cand[nc++] = cd;
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestIdx = -1, bestT = 0;

    /* Phase 1: binary search over candidates sorted by order. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe(mid, now() + slice)) {
            if (cand[mid].T > bestT) {
                bestT = cand[mid].T;
                bestIdx = mid;
            }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: a few more probes just above the best order. */
    int fails = 0;
    int idx = bestIdx < 0 ? 0 : bestIdx + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        if (cand[idx].T <= bestT) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        if (probe(idx, now() + slice)) {
            bestT = cand[idx].T;
            bestIdx = idx;
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (bestIdx < 0) {
        printf("0 0\n");
        return 0;
    }
    apply_cand(&cand[bestIdx]);
    memcpy(mv, bestmv, sizeof(int) * (size_t)B);
    layout();
    memcpy(dg, bestdg, sizeof(int) * (size_t)NDART);
    for (int k = 0; k < NDART; k++) rebuild_dart(k);
    printf("%d %d\n", V, NDART * GN);
    for (int k = 0; k < NDART; k++)
        for (int x = 0; x < GN; x++)
            printf("%d %d\n", dfrom[k] * GN + x, BN + dto[k] * GN + fwdg[k][x]);
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

    # Multi-base group lifts: only graphs with more vertices than the current best are useful.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0]
        hi = mb
        if budget > 2.0 and lo < hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
