"""Mixed affine/semidirect Haar lifts for the bipartite degree-diameter problem.

New construction in this version: the Haar graph of a group G with connection set S
(L_g ~ R_{g s}, s in S) is searched over a wider family of groups. Besides the
affine groups F_q x| H_c, the C engine now also searches the semidirect products
Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), which contain the cyclic, direct
product and genuinely non-abelian cases. Each order N = |G| gets all such groups
(with a bounded random sample of the multipliers r). The lift has 2N vertices and is
d-regular and bipartite. Left translations are transitive on each side, so the
diameter test reduces to two BFS runs, from L_e and from R_e.

Scheduling: candidates are tried in ascending order of N, in rounds with doubling
time slices. A candidate that failed in one round is retried with a longer slice in
the next round. Once a candidate succeeds, only larger orders are tried.
"""
import time

import lib

C_SOURCE = r'''
/* Haar-graph lift search over F_q x| H_c and Z_m x|_r Z_k.
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
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXCAND 100000

typedef struct { int type; int a[4]; int N; } Cand;
/* type 0: F_q x| H_c with a = {q, p, k, c}.
 * type 1: Z_m x|_r Z_k with a = {m, k, r, 0}. */

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
static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
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

/* ------------------------------------------------------------ group state */

static int gtype;            /* 0 = F_q x| H_c, 1 = Z_m x|_r Z_k */
static int GN;
static int GQ, GC;           /* type 0 */
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int GM, GK, GR;       /* type 1 */
static int pw1[MAXN];        /* pw1[b] = r^b mod m */

static void setup_group0(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 0;
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

static void setup_group1(int m, int k, int r) {
    gtype = 1;
    GM = m;
    GK = k;
    GR = r;
    GN = m * k;
    pw1[0] = 1 % m;
    for (int b = 1; b < k; b++) pw1[b] = (int)((long long)pw1[b - 1] * r % m);
}

static void setup_group(const Cand *cd) {
    if (cd->type == 0) setup_group0(cd->a[0], cd->a[1], cd->a[2], cd->a[3]);
    else setup_group1(cd->a[0], cd->a[1], cd->a[2]);
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
        int na = (a + pw1[b] * c) % GM;
        int nb = (b + e) % GK;
        return na * GK + nb;
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int na = (GM - (pw1[nb] * a) % GM) % GM;
        return na * GK + nb;
    }
}

/* ------------------------------------------------------------ Haar graph state */

static int S[MAXD], Sinv[MAXD], bestS[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

/* Vertices: L_g = g (0..GN-1), R_h = GN + h. L_g ~ R_{g s}, so R_h ~ L_{h s^-1}. */
static void set_s(int i, int x) {
    S[i] = x;
    Sinv[i] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][g] = gmul(g, x);
        bwd[i][g] = gmul(g, Sinv[i]);
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

/* Left translations are transitive on each side, so BFS from L_e and R_e decides D. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

static int in_S(int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over the connection set S (size d) in the current group.
 * Returns 1 when cost 0 is reached, 0 on timeout. */
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

static void add_cand(int type, int a0, int a1, int a2, int a3, int N) {
    if (nc >= MAXCAND) return;
    cand[nc].type = type;
    cand[nc].a[0] = a0;
    cand[nc].a[1] = a1;
    cand[nc].a[2] = a2;
    cand[nc].a[3] = a3;
    cand[nc].N = N;
    nc++;
}

/* All candidate groups of order N, appended in random order. */
static void gen_N(int N) {
    int start = nc;
    for (int q = 3; q < MAXQ; q++) {
        if (N % q) continue;
        int c = N / q;
        if (c < 2 || c > q - 1 || (q - 1) % c) continue;
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        add_cand(0, q, p, k, c, N);
    }
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (k == 1) { add_cand(1, m, 1, 0, 0, N); continue; }
        /* Semidirect Z_m x|_r Z_k: r ranges over units with r^k = 1 mod m.
         * Keep r = 1 plus up to two uniformly sampled other valid multipliers. */
        int pick[2] = {1, 1};
        int cnt = 0;
        for (int r = 2; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (cnt <= 2) pick[cnt - 1] = r;
            else {
                int j = rndint(cnt);
                if (j < 2) pick[j] = r;
            }
        }
        add_cand(1, m, k, 1, 0, N);
        for (int t = 0; t < cnt && t < 2; t++) add_cand(1, m, k, pick[t], 0, N);
    }
    for (int i = nc - 1; i > start; i--) {
        int j = start + rndint(i - start + 1);
        Cand tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
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

    for (int N = lo; N <= hi; N++) gen_N(N);
    if (nc == 0) { printf("0 0\n"); return 0; }

    int bestN = 0, bestCi = -1;
    double rem0 = t_end - now();
    double slice = 0.02 * rem0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 2.0) slice = 2.0;

    /* Iterative deepening over candidates in ascending order of N. */
    for (int round = 0; round < 1000; round++) {
        int any = 0;
        for (int ci = 0; ci < nc; ci++) {
            if (cand[ci].N <= bestN) continue;
            double rem = t_end - now();
            if (rem < 0.2) break;
            any = 1;
            double s = slice;
            if (s > rem) s = rem;
            setup_group(&cand[ci]);
            if (search_group(now() + s)) {
                bestN = GN;
                bestCi = ci;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!any || t_end - now() < 0.2) break;
        slice *= 2.0;
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(&cand[bestCi]);
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
    import itertools
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

    # Search: Haar lifts over affine and semidirect groups of order N.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] // 2 + 1, mb // 8)
        hi = mb // 3
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 5.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
