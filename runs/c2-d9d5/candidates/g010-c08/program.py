"""Table-driven Haar lifts over several finite groups for the bipartite degree-diameter problem.

New in this version: the C engine works with any finite group given by a multiplication
table. Besides the affine groups F_q x| H used before, it searches metacyclic groups
Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1). r = 1 gives the abelian groups Z_m x Z_k,
which are non-cyclic when gcd(m, k) > 1. The Haar graph on G with connection set S
(L_g ~ R_{g s}) is d-regular and bipartite. Left translations are automorphisms, so
diameter <= D is checked by two BFS runs, from L_e and from R_e.

Search changes: candidates are sorted by order, with a random tie-break so different
seeds explore different groups of the same order. Each attempt gets 10% of the remaining
time (at least 1 s). Failed candidates are retried in later passes with fresh random
starts.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Table-driven Haar lift search over affine and metacyclic groups.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXN 4096
#define MAXD 32
#define MAXCAND 40000

/* fam 0: F_q x| H, x1 = q, x2 = c.   fam 1: Z_m x|_r Z_k, x1 = m, x2 = k, x3 = r. */
typedef struct { int fam, x1, x2, x3, N; uint64_t rk; } Cand;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

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

static int GN;
static uint16_t MT[MAXN * MAXN];   /* MT[x*GN + y] = x*y, identity code 0 */
static int INV[MAXN];
static int Rp[MAXN];
static int hidx[MAXQ], Hel[MAXC], PWG[MAXQ];

/* Fill INV from the table and check that code 0 acts as identity. */
static int finish_table(void) {
    int N = GN;
    for (int x = 0; x < N; x++)
        if (MT[x] != x) return 0;            /* MT[0*N + x] == x */
    for (int x = 0; x < N; x++) {
        int found = -1;
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        INV[x] = found;
    }
    return 1;
}

/* F_q x| H with H the subgroup of order c in F_q^*. Element (a, h_t) is a*c + t. */
static int setup_fam0(int q, int c) {
    int p, k;
    if (q < 3 || q >= MAXQ || c < 2 || c > MAXC || (q - 1) % c) return 0;
    if (!factor_pp(q, &p, &k)) return 0;
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
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    int N = q * c;
    GN = N;
    for (int x = 0; x < N; x++) {
        int a = x / c, t = x % c;
        for (int y = 0; y < N; y++) {
            int b = y / c, u = y % c;
            int na = ADDT[a][MULT[Hel[t]][b]];
            int nt = hidx[MULT[Hel[t]][Hel[u]]];
            MT[(size_t)x * N + y] = (uint16_t)(na * c + nt);
        }
    }
    return finish_table();
}

/* Metacyclic Z_m x|_r Z_k. Element (a, b) is a*k + b, product (a,b)(c,e) = (a + r^b c, b + e). */
static int setup_fam1(int m, int k, int r) {
    if (m < 2 || k < 2 || m * k > MAXN) return 0;
    int N = m * k;
    GN = N;
    Rp[0] = 1 % m;
    for (int b = 1; b < k; b++) Rp[b] = (Rp[b - 1] * r) % m;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int na = (a + Rp[b] * c) % m;
            int nb = (b + e) % k;
            MT[(size_t)x * N + y] = (uint16_t)(na * k + nb);
        }
    }
    return finish_table();
}

static int setup_group(const Cand *cd) {
    if (cd->fam == 0) return setup_fam0(cd->x1, cd->x2);
    return setup_fam1(cd->x1, cd->x2, cd->x3);
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    int N = GN;
    S[i] = x;
    Sinv[i] = INV[x];
    for (int g = 0; g < N; g++) {
        fwd[i][g] = MT[(size_t)g * N + x];
        bwd[i][g] = MT[(size_t)g * N + Sinv[i]];
    }
}

static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + fwd[i][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int h = v - N;
                for (int i = 0; i < d; i++) {
                    int u = bwd[i][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each side, so BFS from L_e and R_e suffices. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

static int search_group(double until) {
    int N = GN;
    const int iters = 4000;
    while (now() < until) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_S(x, i));
            set_s(i, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(d);
            int x;
            do { x = rndint(N); } while (in_S(x, d));
            int old = S[i];
            set_s(i, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_s(i, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int fam, int x1, int x2, int x3, int N) {
    if (nc >= MAXCAND) return;
    cand[nc].fam = fam;
    cand[nc].x1 = x1;
    cand[nc].x2 = x2;
    cand[nc].x3 = x3;
    cand[nc].N = N;
    cand[nc].rk = rnd();
    nc++;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->rk != y->rk) return x->rk < y->rk ? -1 : 1;
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
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Affine groups F_q x| H. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            add_cand(0, q, c, 0, (int)N);
        }
    }
    /* Metacyclic groups Z_m x|_r Z_k with r^k = 1 mod m (r = 1 gives Z_m x Z_k). */
    for (int m = 2; m <= hi / 2; m++)
        for (int k = 2; k <= hi / m; k++) {
            int N = m * k;
            if (N < lo) continue;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                long x = 1 % m, b = r % m;
                int e = k;
                while (e) {
                    if (e & 1) x = x * b % m;
                    b = b * b % m;
                    e >>= 1;
                }
                if (x != 1 % m) continue;
                add_cand(1, m, k, r, N);
            }
        }

    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int best_idx = -1, bestN = 0;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = 0.1 * rem;
            if (slice < 1.0) slice = 1.0;
            if (slice > rem) slice = rem;
            if (!setup_group(&cand[ci])) continue;
            if (search_group(now() + slice)) {
                bestN = GN;
                best_idx = ci;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&cand[best_idx]);
    for (int i = 0; i < d; i++) set_s(i, bestS[i]);
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

    # Search: table-driven Haar graphs over affine and metacyclic groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
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
