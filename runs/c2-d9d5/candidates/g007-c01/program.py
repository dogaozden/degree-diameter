"""Mixed-group Haar lift search for the bipartite degree-diameter problem.

New in this version: the C engine enumerates two group families. Each family
gives Haar graphs L_g ~ R_{g s} over a finite group of order N:
  * type 0, affine groups F_q x| H with H the order-c subgroup of F_q^*;
  * type 1, semidirect products Z_m x|_r Z_k with r^k = 1 mod m. This includes
    cyclic (k = 1), dihedral (k = 2, r = -1), and direct products (r = 1).
Every candidate group of order N in [lo, hi] is tried in ascending order, with a
fixed share of the remaining time each, and the largest valid order wins. The
group multiplication table is built inside C, so no table is sent over stdin.
The annealing around the incumbent connection set is kept from the parent.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Mixed-group Haar lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Groups of order N in [lo, hi]:
 *   type 0: F_q x| H, H = subgroup of order c of F_q^*   (N = q*c)
 *   type 1: Z_m x|_r Z_k, r^k = 1 mod m, gcd(r, m) = 1   (N = m*k; r = 1 is abelian)
 * Haar graph: L_g ~ R_{g s} for s in S, |S| = d. Identity is element 0.
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
#define MAXN 2048
#define MAXD 32
#define MAXK 8
#define MAXCAND 16384

typedef struct { int type, a, b, r, N; uint32_t key; } Cand;

static int d, D, N;
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
static int PWG[MAXQ];

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ group tables */

static int MUL[MAXN * MAXN];   /* MUL[x*N + y] = x*y, identity = 0 */
static int INV[MAXN];

static int finish_group(void) {
    for (int x = 0; x < N; x++)
        if (MUL[x] != x || MUL[x * N] != x) return 0;   /* identity must be 0 */
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

/* Type 0: element (a, j) coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t), and h_j h_t = h_{(j+t) mod c}. */
static int make_affine(int q, int c) {
    int p, k;
    if (q < 3 || q >= MAXQ || c < 2 || (q - 1) % c) return 0;
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
    int h[MAXC];
    for (int j = 0; j < c; j++) h[j] = PWG[(j * step) % (q - 1)];
    N = q * c;
    if (N > MAXN) return 0;
    for (int a = 0; a < q; a++)
        for (int j = 0; j < c; j++)
            for (int b = 0; b < q; b++)
                for (int t = 0; t < c; t++)
                    MUL[(a * c + j) * N + (b * c + t)] =
                        ADDT[a][MULT[h[j]][b]] * c + (j + t) % c;
    return finish_group();
}

/* Type 1: element (a, b) coded as a*k + b.
 * Product (a, b)(c, e) = (a + r^b c, b + e), needs r^k = 1 mod m. */
static int make_semi(int m, int k, int r) {
    if (m < 2 || k < 1 || k > MAXK || m > MAXN) return 0;
    if (gcd_i(r, m) != 1) return 0;
    if (powmod(r, k, m) != 1 % m) return 0;
    N = m * k;
    if (N > MAXN) return 0;
    int rp[MAXK];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long na = ((long)a + (long)rp[b] * c) % m;
            MUL[x * N + y] = (int)na * k + (b + e) % k;
        }
    }
    return finish_group();
}

static int setup(const Cand *cd) {
    if (cd->type == 0) return make_affine(cd->a, cd->b);
    return make_semi(cd->a, cd->b, cd->r);
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..N-1), R_h = N + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = INV[x];
    for (int g = 0; g < N; g++) {
        fwd[i][g] = MUL[g * N + x];
        bwd[i][g] = MUL[g * N + Sinv[i]];
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

/* Left translations are transitive on each side, so two BFS runs decide the diameter. */
static long cover_cost(void) {
    int V = 2 * N;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(N));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Iterated annealing over the connection set S (size d) in the current group.
 * Round 1 starts from a random set. Later rounds start from the incumbent with two
 * elements replaced, at a lower starting temperature.
 * Returns 1 on cost 0 (S holds the valid set), 0 on timeout. */
static int search_group(double until) {
    const int iters = 8000;
    int have = 0;
    long bestc = 0;
    int incS[MAXD];
    while (now() < until) {
        if (!have) {
            for (int i = 0; i < d; i++) {
                int x;
                do { x = rndint(N); } while (in_S(x, i));
                set_s(i, x);
            }
        } else {
            for (int i = 0; i < d; i++) set_s(i, incS[i]);
            for (int t = 0; t < 2; t++) {
                int i = rndint(d), x;
                do { x = rndint(N); } while (in_S(x, d));
                set_s(i, x);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
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
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incS, S, sizeof(int) * (size_t)d);
        }
    }
    return 0;
}

static void print_result(void) {
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + fwd[i][g]);
}

/* ------------------------------------------------------------ candidate groups */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(int type, int a, int b, int r, int n) {
    if (nc >= MAXCAND) return;
    cand[nc].type = type;
    cand[nc].a = a;
    cand[nc].b = b;
    cand[nc].r = r;
    cand[nc].N = n;
    cand[nc].key = (uint32_t)rnd();
    nc++;
}

static int cmp_cand(const void *A, const void *B) {
    const Cand *x = (const Cand *)A, *y = (const Cand *)B;
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
    if (hi > MAXN) hi = MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long n = (long)q * c;
            if (n < lo || n > hi) continue;
            add_cand(0, q, c, 0, (int)n);
        }
    }
    for (int k = 1; k <= MAXK; k++) {
        int m0 = (lo + k - 1) / k;
        if (m0 < 2) m0 = 2;
        for (int m = m0; (long)m * k <= hi; m++) {
            int n = m * k;
            for (int r = 1; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                add_cand(1, m, k, r, n);
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending order: each success raises the bar, so the final answer is the
     * largest order that succeeded. Each attempt gets 15% of the remaining time
     * (at least 1.5 s). */
    int bestN = 0, have = 0;
    Cand bestc;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand cd = cand[ci];
        if (cd.N <= bestN) continue;
        double slice = 0.15 * rem;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        if (!setup(&cd)) continue;
        if (search_group(now() + slice)) {
            bestN = N;
            bestc = cd;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    setup(&bestc);
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

    # Search: Haar graphs over affine and semidirect groups of order N in [lo, hi].
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
