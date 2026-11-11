"""Haar-lift search over several group families for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs over F_q x| H. This
version widens the family. For each order N in the window it tries Haar graphs
(L_g ~ R_{g*s}, s in a d-element set S) over:
  - cyclic groups Z_N,
  - abelian groups Z_a x Z_b,
  - dihedral groups D_m (order 2m),
  - metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1),
  - the parent's F_q x| H family, kept as a hedge.
Candidates are ordered by N ascending, with random order inside each N. The C engine
spends a slice of the remaining time on each candidate (clamped to [1 s, 8 s]), and
later passes retry the candidates that failed earlier with fresh random starts.

Diameter is checked with two BFS runs (from L_e and R_e), because left translations
act transitively on each side. Every result is re-checked with lib.is_valid, and the
fallback K_{d,d} (valid for D >= 2) is kept if nothing better passes.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Haar-lift search over several group families.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXN 3400
#define MAXD 32
#define MAXCAND 30000

enum { FAM_CYC = 0, FAM_ABEL = 1, FAM_DIH = 2, FAM_SEMI = 3, FAM_FQ = 4 };

typedef struct { int fam, N, A, B, R, p, k, key; } Cand;

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
static long powmod_i(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
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
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;   /* zero divisor: reducible */
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

static int curfam, curA, curB, curR;
static int GN;
static int PWR[MAXN];
static int Hel[MAXQ], hidx[MAXQ], PWG[MAXQ];
static uint16_t TAB[MAXN * MAXN];
static int INV[MAXN];

/* Element codings:
 *  CYC : x in Z_N.
 *  ABEL: x = i*B + j, i in Z_A, j in Z_B.
 *  DIH : x = s*m + i (m = B), r^i s^s; (s1,i1)(s2,i2) = (s1+s2, i1 + (-1)^s1 i2).
 *  SEMI: x = a*B + b, a in Z_A (m = A), b in Z_B (k = B); (a,b)(c,e) = (a + r^b c, b + e).
 *  FQ  : x = a*B + j, a in F_q (q = A), h_j in H of order B; (a,h_j)(b,h_t) = (a + h_j b, h_j h_t).
 * Identity is 0 in every family. */
static inline int gmul(int x, int y) {
    int A = curA, B = curB, N = GN;
    switch (curfam) {
    case FAM_CYC: {
        int s = x + y;
        return s >= N ? s - N : s;
    }
    case FAM_ABEL: {
        int i = x / B + y / B;
        if (i >= A) i -= A;
        int j = x % B + y % B;
        if (j >= B) j -= B;
        return i * B + j;
    }
    case FAM_DIH: {
        int m = B;
        int s1 = x / m, i1 = x % m, s2 = y / m, i2 = y % m;
        int t = s1 ? (m - i2) % m : i2;
        int i = (i1 + t) % m;
        return ((s1 + s2) & 1) * m + i;
    }
    case FAM_SEMI: {
        int a = x / B, b = x % B, c = y / B, e = y % B;
        int na = (int)(((long)a + (long)PWR[b] * c) % A);
        int nb = (b + e) % B;
        return na * B + nb;
    }
    default: {
        int a = x / B, j = x % B, b = y / B, t = y % B;
        int na = ADDT[a][MULT[Hel[j]][b]];
        int nt = hidx[MULT[Hel[j]][Hel[t]]];
        return na * B + nt;
    }
    }
}

static void setup_fq(int q, int c, int p, int k) {
    build_field(q, p, k);
    int g = 0;
    for (int g0 = 2; g0 < q && !g; g0++) {
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
}

static void setup_cand(const Cand *c) {
    curfam = c->fam;
    curA = c->A;
    curB = c->B;
    curR = c->R;
    GN = c->N;
    int N = GN;
    if (curfam == FAM_SEMI) {
        PWR[0] = 1 % curA;
        for (int b = 1; b < curB; b++)
            PWR[b] = (int)((long)PWR[b - 1] * curR % curA);
    }
    if (curfam == FAM_FQ) setup_fq(c->A, c->B, c->p, c->k);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            TAB[x * N + y] = (uint16_t)gmul(x, y);
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (TAB[x * N + y] == 0) { INV[x] = y; break; }
    }
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
        fwd[i][g] = TAB[g * N + x];
        bwd[i][g] = TAB[g * N + Sinv[i]];
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

/* Simulated annealing over the connection set S (size d) in the current group. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
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

static void addc(int fam, int N, int A, int B, int R, int p, int k) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.fam = fam;
    c.N = N;
    c.A = A;
    c.B = B;
    c.R = R;
    c.p = p;
    c.k = k;
    c.key = rndint(1 << 30);
    cand[nc++] = c;
}

static void enumerate_cands(int lo, int hi) {
    for (int N = lo; N <= hi; N++) {
        addc(FAM_CYC, N, 0, 0, 0, 0, 0);
        for (int a = 2; a * a <= N; a++)
            if (N % a == 0 && N / a >= 2) addc(FAM_ABEL, N, a, N / a, 0, 0, 0);
        if (N % 2 == 0 && N / 2 >= 3) addc(FAM_DIH, N, 0, N / 2, 0, 0, 0);
        for (int m = 3; m <= N / 2; m++) {
            if (N % m) continue;
            int k = N / m;
            if (k < 2) continue;
            for (int r = 2; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_i(r, k, m) != 1 % m) continue;
                addc(FAM_SEMI, N, m, k, r, 0, 0);
            }
        }
        for (int q = 3; q < MAXQ; q++) {
            if (N % q) continue;
            int c = N / q;
            if (c < 2 || (q - 1) % c) continue;
            int p, k;
            if (!factor_pp(q, &p, &k)) continue;
            addc(FAM_FQ, N, q, c, 0, p, k);
        }
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->N != y->N) return x->N < y->N ? -1 : 1;
    if (x->key != y->key) return x->key < y->key ? -1 : 1;
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
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    enumerate_cands(lo, hi);
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    int bestN = 0, best_ci = -1;
    for (int pass = 0; pass < 100000; pass++) {
        int tried = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            tried = 1;
            double slice = rem / 6.0;
            if (slice < 1.0) slice = 1.0;
            if (slice > 8.0) slice = 8.0;
            if (slice > rem) slice = rem;
            setup_cand(&cand[ci]);
            if (search_group(now() + slice)) {
                bestN = GN;
                best_ci = ci;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!tried || t_end - now() < 0.3) break;
    }

    if (best_ci < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&cand[best_ci]);
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

    # Search: Haar graphs over several group families, orders from the record window up.
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
