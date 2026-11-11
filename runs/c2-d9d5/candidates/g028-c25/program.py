"""Two-orbit voltage lifts over mixed affine and metacyclic groups for the bipartite degree-diameter problem.

Idea in this version: the parent searched only affine groups F_q x| H. This version adds
metacyclic semidirect products Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1), which exist for
many more orders N, so the binary search over group order has a finer grid near the record.
Each candidate group is a triple (family, parameters). Candidates are sorted by order, and the
C search binary-searches over distinct orders, trying up to three random group realisations
(affine or metacyclic) at each order.

The lift is K left orbits and K right orbits over G, with d darts per left orbit and d darts
per right orbit. Left translation is an automorphism, so diameter is checked by one BFS per
orbit representative (2K BFS runs). Moves are voltage changes and swaps of target orbits. The
best valid graph wins, with the K = 2 stage first and the K = 1 Haar-type stage after it.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lift search over affine and metacyclic groups.
 * Usage: prog d D seed time_limit lo hi K     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertices: left L^a_x = a*N + x (a < K), right R^b_y = K*N + b*N + y.
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
#define MAXK 2
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 80000

/* mode 0: affine F_q x| Z_c with a1 = q, a2 = c.
 * mode 1: metacyclic Z_m x|_r Z_k with a1 = m, a2 = k, a3 = r. */
typedef struct { int mode, a1, a2, a3, N; unsigned tie; } Cand;

static int K, d, D, GN, nd;
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

/* ------------------------------------------------------------ group state */

static int GMODE = 0;                 /* 0 affine, 1 metacyclic */
static int GC_ = 1;                   /* affine: |H| */
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int MM = 1, KK = 1, RR = 0;    /* metacyclic: m, k, r */
static int PW[MAXN];                  /* metacyclic: r^b mod m, b < k */

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GN = q * c;
    GC_ = c;
    GMODE = 0;
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

static int aff_mul(int x, int y) {
    int a = x / GC_, j = x % GC_, b = y / GC_, t = y % GC_;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC_ + HM[j * GC_ + t];
}
static int aff_inv(int x) {
    int a = x / GC_, j = x % GC_;
    int jn = (GC_ - j) % GC_;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC_ + jn;
}

static void load_sd(int m, int k, int r) {
    MM = m;
    KK = k;
    RR = r;
    GN = m * k;
    GMODE = 1;
    PW[0] = 1 % m;
    for (int i = 1; i < k; i++) PW[i] = (int)(((long)PW[i - 1] * r) % m);
}
/* Element (a, b) is coded a*k + b. (a,b)(c,e) = (a + r^b c, b + e), with r^k = 1 mod m. */
static int sd_mul(int x, int y) {
    int a = x / KK, b = x - a * KK;
    int c = y / KK, e = y - c * KK;
    long t = ((long)a + (long)PW[b] * c) % MM;
    int nb = b + e;
    if (nb >= KK) nb -= KK;
    return (int)t * KK + nb;
}
/* Inverse of (a, b) is (-r^(k-b) a, k-b) with k-b taken mod k. */
static int sd_inv(int x) {
    int a = x / KK, b = x - a * KK;
    int nb = (KK - b) % KK;
    long c = (MM - ((long)PW[nb] * a) % MM) % MM;
    return (int)c * KK + nb;
}

static inline int gmul(int x, int y) { return GMODE == 0 ? aff_mul(x, y) : sd_mul(x, y); }
static inline int ginv(int x) { return GMODE == 0 ? aff_inv(x) : sd_inv(x); }

static void load_group(Cand c) {
    if (c.mode == 0) {
        int p, k;
        factor_pp(c.a1, &p, &k);
        setup_affine(c.a1, p, k, c.a2);
    } else {
        load_sd(c.a1, c.a2, c.a3);
    }
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart t = a*d + i leaves left orbit a: L^a_x ~ R^{tb[t]}_{x * vg[t]}. */
static void set_dart(int t, int x) {
    vg[t] = x;
    int ix = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        invT[t][g] = gmul(g, ix);
    }
}

static void rebuild_inc(void) {
    for (int b = 0; b < K; b++) cnt_in[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        if (cnt_in[b] < MAXD) inc_t[b][cnt_in[b]++] = t;
    }
}

static void random_init(void) {
    int list[MAXND];
    int p = 0;
    for (int b = 0; b < K; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

static int bfs_count(int src) {
    int V2 = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < V2) {
                int a = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int t = a * d + i;
                    int u = V2 + tb[t] * GN + fwdT[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - V2;
                int b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = inc_t[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* One BFS per orbit representative suffices (left translations are transitive automorphisms). */
static long cover_cost(void) {
    long V = 2L * K * GN;
    long c = 0;
    for (int a = 0; a < K; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < K; b++) c += V - bfs_count(K * GN + b * GN);
    return c + 1000L * dup_count();
}

static void save_best(void) {
    memcpy(bestTb, tb, sizeof(int) * (size_t)nd);
    memcpy(bestVg, vg, sizeof(int) * (size_t)nd);
}

static int search_group(double until) {
    const int iters = 6000;
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            long c2;
            if (K > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd);
                int x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int V = 2 * K * GN;
    printf("%d %d\n", V, K * GN * d);
    for (int a = 0; a < K; a++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int t = a * d + i;
                int u = K * GN + tb[t] * GN + fwdT[t][x];
                printf("%d %d\n", a * GN + x, u);
            }
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;
static int gStart[MAXCAND], gCount[MAXCAND], gC = 0;
static Cand bestC;
static int have_best = 0;

static void add_cand(int mode, int a1, int a2, int a3, int N) {
    if (nc >= MAXCAND) return;
    Cand c;
    c.mode = mode; c.a1 = a1; c.a2 = a2; c.a3 = a3; c.N = N;
    c.tie = (unsigned)rnd();
    cand[nc++] = c;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

static int cmp_cand(const void *A, const void *B) {
    const Cand *a = (const Cand *)A, *b = (const Cand *)B;
    if (a->N != b->N) return a->N < b->N ? -1 : 1;
    if (a->tie != b->tie) return a->tie < b->tie ? -1 : 1;
    return 0;
}

/* Try up to three realisations of the group order at gi; keep the first valid one. */
static int try_group(int gi, double until) {
    int cnt = gCount[gi], st = gStart[gi];
    int tries = cnt < 3 ? cnt : 3;
    for (int j = 0; j < tries; j++) {
        double rem = until - now();
        if (rem < 0.1) return 0;
        double slice = rem / (double)(tries - j);
        load_group(cand[st + j]);
        if (search_group(now() + slice)) {
            bestC = cand[st + j];
            save_best();
            have_best = 1;
            return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 8) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    K = atoi(argv[7]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3 || K < 1 || K > MAXK) {
        printf("0 0\n");
        return 0;
    }
    nd = K * d;
    if (hi > MAXN) hi = MAXN;
    if (lo < 2) lo = 2;
    if (lo > hi) {
        printf("0 0\n");
        return 0;
    }

    /* Affine candidates: F_q x| Z_c with c | q-1. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N < lo || N > hi) continue;
            add_cand(0, q, c, 0, N);
        }
    }
    /* Metacyclic candidates: Z_m x|_r Z_k with N = m*k, gcd(r,m) = 1, r^k = 1 mod m. */
    for (int N = lo; N <= hi; N++) {
        for (int k = 1; k <= N; k++) {
            if (N % k) continue;
            int m = N / k;
            if (m == 1) { add_cand(1, 1, N, 0, N); continue; }
            if (k == 1) { add_cand(1, m, 1, 1, N); continue; }
            for (int r = 1; r < m; r++) {
                if (gcdl(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                add_cand(1, m, k, r, N);
            }
        }
    }
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Group candidates by order. */
    for (int i = 0; i < nc;) {
        int j = i;
        while (j < nc && cand[j].N == cand[i].N) j++;
        gStart[gC] = i;
        gCount[gC] = j - i;
        gC++;
        i = j;
    }

    /* Phase 1: binary search over distinct orders. */
    int li = 0, hiG = gC - 1, gbest = -1;
    while (li <= hiG && now() < t_end) {
        int mid = (li + hiG) / 2;
        double rem = t_end - now();
        double slice = rem * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_group(mid, now() + slice)) {
            gbest = mid;
            li = mid + 1;
        } else {
            hiG = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next orders above the best. */
    int fails = 0;
    int gi = gbest < 0 ? 0 : gbest + 1;
    while (gi < gC && now() < t_end && fails < 2) {
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (try_group(gi, now() + slice)) {
            gbest = gi;
            fails = 0;
        } else {
            fails++;
        }
        gi++;
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    load_group(bestC);
    memcpy(tb, bestTb, sizeof(int) * (size_t)nd);
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bestVg[t]);
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


def _orbit_lift_search(d, D, seed, budget, lo, hi, K):
    """Run the C engine with K left and K right orbits over mixed affine/metacyclic groups."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, K],
                     stdin_graph=None, timeout=budget + 8.0)
    return lib.parse_graph_text(text)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - t0)

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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)

        # Stage A: two-orbit lifts (4|G| vertices) over mixed affine/metacyclic groups.
        budget = 0.5 * left() - 2.0
        lo = max(best[0] // 4 + 1, 2)
        hi = mb // 4
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_lift_search(d, D, seed, budget, lo, hi, 2))
            except Exception:
                pass

        # Stage B: single-orbit lifts (2|G| vertices) with the remaining time.
        budget = 0.75 * left() - 2.0
        lo = max(best[0] // 2 + 1, 2)
        hi = mb // 2
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_lift_search(d, D, seed + 1, budget, lo, hi, 1))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
