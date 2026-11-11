"""Bi-coset (2+2 base) voltage lifts over F_q x| H for the bipartite degree-diameter problem.

Family: a base bipartite graph with m vertices on each side (m = 1 or 2) and
block sets S[x][y] of group elements in G = F_q x| H. Vertex (A_x, g) is joined to
(B_y, g*s) for every s in S[x][y]. For m = 2 the block sizes are (a, d-a; d-a, a),
so every vertex has degree d. Left multiplication is an automorphism, so the
diameter is decided by BFS from the 2m base vertices (A_x, e) and (B_y, e).

m = 1 is the Haar lift used by the previous version. m = 2 is new: its order is
4|G|, so it reaches the same vertex counts with groups about half as large, and
it has different structure. One C run handles both families: candidates are
sorted by vertex count and searched in ascending order from a lower bound.
Each search is an iterated annealing that perturbs the incumbent connection sets.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-coset lift search over F_q x| H.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the vertex count of the output.
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
#define MAXN 4800
#define MAXD 32
#define MAXK 64
#define MAXV (4 * MAXN)
#define MAXCAND 20000

typedef struct { int m, a, q, p, k, c, N; long total; } Cand;

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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). c = 1 gives the additive group. */
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

/* ------------------------------------------------------------ bi-coset state */

/* Blocks k = 0..K_-1: block k joins A_{bx[k]} to B_{by[k]} with connection element E[k].
 * Vertex ids: A_x, g -> x*N + g;  B_y, h -> m*N + y*N + h.  (A_x,g) ~ (B_y, g*E[k]). */
static int m_, K_;
static int bx[MAXK], by[MAXK];
static int E[MAXK], Sinv[MAXK], incE[MAXK], bestE[MAXK];
static int fwd[MAXK][MAXN], bwd[MAXK][MAXN];
static int alist[2][MAXK], acnt[2], blist[2][MAXK], bcnt[2];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void layout(int m, int dd, int a) {
    m_ = m;
    K_ = 0;
    if (m == 1) {
        for (int i = 0; i < dd; i++) { bx[K_] = 0; by[K_] = 0; K_++; }
    } else {
        int sizes[4] = {a, dd - a, dd - a, a};
        int xs[4] = {0, 0, 1, 1};
        int ys[4] = {0, 1, 0, 1};
        for (int b = 0; b < 4; b++)
            for (int i = 0; i < sizes[b]; i++) { bx[K_] = xs[b]; by[K_] = ys[b]; K_++; }
    }
    acnt[0] = acnt[1] = 0;
    bcnt[0] = bcnt[1] = 0;
    for (int k = 0; k < K_; k++) {
        alist[bx[k]][acnt[bx[k]]++] = k;
        blist[by[k]][bcnt[by[k]]++] = k;
    }
}

static void set_elem(int k, int x) {
    E[k] = x;
    Sinv[k] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[k][g] = gmul(g, x);
        bwd[k][g] = gmul(g, Sinv[k]);
    }
}

static int in_block(int k, int x) {
    for (int j = 0; j < K_; j++)
        if (j != k && bx[j] == bx[k] && by[j] == by[k] && E[j] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, mN = m_ * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < mN) {
                int x = v / N, g = v - x * N;
                for (int t = 0; t < acnt[x]; t++) {
                    int k = alist[x][t];
                    int u = mN + by[k] * N + fwd[k][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - mN, y = w / N, h = w - y * N;
                for (int t = 0; t < bcnt[y]; t++) {
                    int k = blist[y][t];
                    int u = bx[k] * N + bwd[k][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms, so BFS from one vertex per base class decides
 * the diameter. Cost 0 means every source reaches all vertices within D. */
static long cover_cost(void) {
    long V = 2L * m_ * GN, c = 0;
    for (int x = 0; x < m_; x++) c += V - bfs_count(x * GN);
    for (int y = 0; y < m_; y++) c += V - bfs_count(m_ * GN + y * GN);
    return c;
}

/* Iterated annealing over the block elements. Round 1 starts random; later rounds
 * perturb the incumbent (two blocks re-drawn) and anneal at a lower temperature.
 * Returns 1 when cost 0 is reached (E holds the valid solution), 0 on timeout. */
static int search_group(double until) {
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    while (now() < until) {
        if (!have) {
            for (int k = 0; k < K_; k++) E[k] = -1;
            for (int k = 0; k < K_; k++) {
                int x;
                do { x = rndint(GN); } while (in_block(k, x));
                E[k] = x;
            }
        } else {
            for (int k = 0; k < K_; k++) E[k] = incE[k];
            for (int t = 0; t < 2; t++) {
                int k = rndint(K_), x;
                do { x = rndint(GN); } while (in_block(k, x));
                E[k] = x;
            }
        }
        for (int k = 0; k < K_; k++) set_elem(k, E[k]);
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int k = rndint(K_), x;
            do { x = rndint(GN); } while (in_block(k, x));
            int old = E[k];
            set_elem(k, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_elem(k, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            for (int k = 0; k < K_; k++) incE[k] = E[k];
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN, mN = m_ * N;
    printf("%d %d\n", 2 * mN, mN * d);
    for (int x = 0; x < m_; x++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < acnt[x]; t++) {
                int k = alist[x][t];
                printf("%d %d\n", x * N + g, mN + by[k] * N + fwd[k][g]);
            }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
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

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int m = 1; m <= 2; m++) {
        int as[2], na = 0;
        if (m == 1) {
            as[na++] = d;
        } else {
            int a1 = d / 2;
            if (a1 >= 1 && a1 <= d - 1) as[na++] = a1;
            if (1 <= d - 1 && 1 != a1) as[na++] = 1;
        }
        for (int ai = 0; ai < na; ai++)
            for (int q = 3; q < MAXQ; q++) {
                int p, k;
                if (!factor_pp(q, &p, &k)) continue;
                for (int c = 1; c <= q - 1; c++) {
                    if ((q - 1) % c) continue;
                    long N = (long)q * c;
                    if (N < d + 1 || N > MAXN) continue;
                    long total = 2L * m * N;
                    if (total < lo || total > hi) continue;
                    if (nc < MAXCAND) {
                        Cand cd = {m, as[ai], q, p, k, c, (int)N, total};
                        cand[nc++] = cd;
                    }
                }
            }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending ladder: skip anything not above the best total found so far.
     * Each attempt gets 15% of the remaining time, clamped to [0.7 s, 6 s]. */
    long bestTotal = 0;
    int bi = -1;
    for (int ci = 0; ci < nc; ci++) {
        if (cand[ci].total <= bestTotal) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.15 * rem;
        if (slice < 0.7) slice = 0.7;
        if (slice > 6.0) slice = 6.0;
        if (slice > rem) slice = rem;
        layout(cand[ci].m, d, cand[ci].a);
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        if (search_group(now() + slice)) {
            bestTotal = cand[ci].total;
            bi = ci;
            memcpy(bestE, E, sizeof(int) * (size_t)K_);
        }
    }

    if (bi < 0) {
        printf("0 0\n");
        return 0;
    }
    layout(cand[bi].m, d, cand[bi].a);
    setup_group(cand[bi].q, cand[bi].p, cand[bi].k, cand[bi].c);
    for (int k = 0; k < K_; k++) set_elem(k, bestE[k]);
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

    # Search: bi-coset lifts (m = 1 Haar and m = 2 two-by-two base) over F_q x| H.
    if 2 <= d <= 32 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 6)
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
