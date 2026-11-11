"""Two-base-vertex group lifts for the bipartite degree-diameter problem.

New in this version: the parent's Haar graph is a lift of a base graph with one
vertex per side. Here the base graph has B vertices per side (B = 1 or 2) and
d darts leave each left base vertex and enter each right base vertex. For B = 2
the dart counts form the matrix [[k, d-k], [d-k, k]], with 1 <= k <= d-1. A dart
(a, b, g) joins L^a_x to R^b_{x g} for every x in the group G. The lift has
2*B*|G| vertices, and every vertex has degree d.

Left multiplication by G is an automorphism, so the diameter test needs only
2B breadth-first searches, one from each base vertex at the identity. This gives
order 4|G| for B = 2, which is a family the parent does not search.

The C engine ranks candidates (affine groups F_q x| H and, for B = 2, cyclic
groups) by vertex count in ascending order, with a ratchet on the best valid
order so far. Each candidate gets a bounded time slice, and passes repeat until
time runs out. Python keeps the parent's constructions as fallbacks and validates
the result with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Base-lift search: bipartite lifts with B base vertices per side over a group G of order N.
 * Usage: prog d D seed time_limit lo hi     (lo, hi bound the vertex count 2*B*N; stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 1024
#define MAXN 2048
#define MAXD 32
#define MAXT 64
#define MAXV 8192
#define MAXCAND 40000

typedef struct { int B, kind, q, p, k, c, N, V; } Cand;

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
    if (k == 1) {
        for (int a = 0; a < q; a++)
            for (int b = 0; b < q; b++)
                MULT[a][b] = (a * b) % q;
    } else {
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
    }
    built_q = q;
}

/* ------------------------------------------------------------ groups */

/* Cyclic Z_N (kind 0) or F_q x| H with |H| = c (kind 1). Elements 0..N-1, identity 0. */
static int GN, GC, GQ;
static int Hel[MAXQ], hidx[MAXQ], PWG[MAXQ];
static int MTAB[MAXN * MAXN];   /* MTAB[x*N + y] = x*y */
static int INVT[MAXN];

static int gmul(int x, int y) {
    int c = GC;
    int a = x / c, j = x - a * c, b = y / c, t = y - b * c;
    int na = ADDT[a][MULT[Hel[j]][b]];
    int nt = hidx[MULT[Hel[j]][Hel[t]]];
    return na * c + nt;
}

static int ginv(int x) {
    int c = GC;
    int a = x / c, j = x - a * c;
    int jn = (c - j) % c;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * c + jn;
}

static void setup_group(const Cand *cd) {
    int N = cd->N;
    GN = N;
    if (cd->kind == 0) {
        for (int x = 0; x < N; x++) {
            INVT[x] = (N - x) % N;
            for (int y = 0; y < N; y++) MTAB[x * N + y] = (x + y) % N;
        }
        return;
    }
    int q = cd->q, c = cd->c, p = cd->p, k = cd->k;
    build_field(q, p, k);
    GC = c;
    GQ = q;
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
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[x * N + y] = gmul(x, y);
    for (int x = 0; x < N; x++) INVT[x] = ginv(x);
}

/* ------------------------------------------------------------ base graph and darts */

static int B, T, curk;
static int dsrc[MAXT], dtgt[MAXT], dg[MAXT];
static int outL[2][MAXD], inR[2][MAXD];
static int fwd[MAXT][MAXN], bwd[MAXT][MAXN];

/* Dart counts m[a][b]: B = 1 gives [[d]]; B = 2 gives [[k, d-k], [d-k, k]]. */
static void layout(int kk) {
    int m[2][2];
    m[0][0] = m[0][1] = m[1][0] = m[1][1] = 0;
    if (B == 1) {
        m[0][0] = d;
    } else {
        m[0][0] = kk;
        m[0][1] = d - kk;
        m[1][0] = d - kk;
        m[1][1] = kk;
    }
    int oc[2] = {0, 0}, ic[2] = {0, 0};
    T = 0;
    for (int a = 0; a < B; a++)
        for (int b = 0; b < B; b++)
            for (int r = 0; r < m[a][b]; r++) {
                int t = T++;
                dsrc[t] = a;
                dtgt[t] = b;
                outL[a][oc[a]++] = t;
                inR[b][ic[b]++] = t;
            }
}

/* Dart t uses group element x: fwd[t][y] = y*x, bwd[t][y] = y*x^-1. */
static void set_dart(int t, int x) {
    int N = GN;
    dg[t] = x;
    int xi = INVT[x];
    for (int y = 0; y < N; y++) {
        fwd[t][y] = MTAB[y * N + x];
        bwd[t][y] = MTAB[y * N + xi];
    }
}

/* True if dart t cannot use x: another dart u < lim in the same block already has x. */
static int conflict(int t, int x, int lim) {
    int blk = dsrc[t] * B + dtgt[t];
    for (int u = 0; u < lim; u++)
        if (u != t && dsrc[u] * B + dtgt[u] == blk && dg[u] == x) return 1;
    return 0;
}

/* ------------------------------------------------------------ cost */

/* Vertices: left (a,x) = a*N + x; right (b,y) = B*N + b*N + y. Edge: L^a_x ~ R^b_{x g}. */
static int VV;
static int vis[MAXV], que[MAXV], stamp_ = 0;

static int reach(int src) {
    int N = GN, BN = B * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int a = v / N, x = v - a * N;
                for (int i = 0; i < d; i++) {
                    int t = outL[a][i];
                    int u = BN + dtgt[t] * N + fwd[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN;
                int b = w / N, y = w - b * N;
                for (int i = 0; i < d; i++) {
                    int t = inR[b][i];
                    int u = dsrc[t] * N + bwd[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity within each fiber: BFS from the identity of each base vertex
 * (left and right) covers all pairs. Cost 0 iff diameter <= D. */
static long cost_all(void) {
    int N = GN;
    long c = 0;
    for (int a = 0; a < B; a++) c += VV - reach(a * N);
    for (int b = 0; b < B; b++) c += VV - reach(B * N + b * N);
    return c;
}

/* ------------------------------------------------------------ search */

static int search_cand(double until) {
    const int iters = 3000;
    int N = GN;
    while (now() < until) {
        curk = (B == 1) ? d : 1 + rndint(d - 1);
        layout(curk);
        for (int t = 0; t < T; t++) {
            int x;
            do { x = rndint(N); } while (conflict(t, x, t));
            set_dart(t, x);
        }
        long cost = cost_all();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 31) == 0 && now() > until) return 0;
            double Tm = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(T);
            int x;
            do { x = rndint(N); } while (conflict(t, x, T));
            int old = dg[t];
            set_dart(t, x);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ output */

static Cand bestc;
static int bestB_s, bestk_s, bestdg_s[MAXT];

static void print_result(void) {
    B = bestB_s;
    setup_group(&bestc);
    VV = 2 * B * GN;
    layout(bestk_s);
    for (int t = 0; t < T; t++) set_dart(t, bestdg_s[t]);
    int N = GN;
    printf("%d %d\n", VV, B * N * d);
    for (int a = 0; a < B; a++)
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++) {
                int t = outL[a][i];
                printf("%d %d\n", a * N + x, B * N + dtgt[t] * N + fwd[t][x]);
            }
}

static int cmp_cand(const void *A, const void *Bp) {
    const Cand *x = (const Cand *)A, *y = (const Cand *)Bp;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->kind != y->kind) return y->kind - x->kind;   /* affine first on ties */
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int BB = 1; BB <= 2; BB++) {
        int nlo = (lo + 2 * BB - 1) / (2 * BB), nhi = hi / (2 * BB);
        if (nhi > MAXN) nhi = MAXN;
        if (nlo < d + 1) nlo = d + 1;
        if (nlo > nhi) continue;
        if (BB == 2) {   /* cyclic base-2 lifts are a second family to try */
            for (int N = nlo; N <= nhi && nc < MAXCAND; N++) {
                Cand cd = {BB, 0, 0, 0, 0, 0, N, 2 * BB * N};
                cand[nc++] = cd;
            }
        }
        for (int q = 3; q < MAXQ; q++) {
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            for (int c = 2; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long N = (long)q * c;
                if (N < nlo || N > nhi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {BB, 1, q, p, k, c, (int)N, 2 * BB * (int)N};
                    cand[nc++] = cd;
                }
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ratchet: only candidates with more vertices than the best found so far.
     * Repeated passes give failed candidates fresh randomized attempts. */
    int bestV = 0, found = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].V <= bestV) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.12 * rem;
            if (slice < 0.6) slice = 0.6;
            if (slice > 2.5) slice = 2.5;
            if (slice > rem) slice = rem;
            B = cand[ci].B;
            setup_group(&cand[ci]);
            VV = 2 * B * GN;
            layout(B == 1 ? d : 2);   /* sets T so the dart arrays are sized */
            if (search_cand(now() + slice)) {
                bestV = cand[ci].V;
                bestc = cand[ci];
                bestB_s = B;
                bestk_s = curk;
                memcpy(bestdg_s, dg, sizeof(int) * (size_t)T);
                found = 1;
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
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

    # Search: two-base-vertex and one-base-vertex group lifts, vertex count in [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 4)
        hi = mb // 3
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
