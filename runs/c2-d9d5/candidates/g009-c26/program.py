"""Two-orbit voltage lifts over mixed group families for the bipartite degree-diameter problem.

The parent searched voltage lifts over affine groups F_q x| C_c only. This version
adds a new group family: metacyclic groups Z_m x| Z_k (element (a, b) coded as
a*k + b, product (a, b)(c, e) = (a + r^b c, b + e), with r^k = 1 mod m and
gcd(r, m) = 1). These exist for many more orders N than the affine family, so the
group-order grid is finer and can hit values such as 624 (record 2496 = 4 * 624)
and values just above it that the affine orders skip.

Each group order N gets up to PERN candidate groups (affine first, then random
metacyclic ones with a random starting r). The C engine binary-searches over the
orders, and within an order it splits the probe time evenly across its candidates.

Lift structure (unchanged from the parent): K left orbits and K right orbits over G,
left orbit a has d darts (a, b, g) with L^a_x ~ R^b_{x g}, every right orbit receives
exactly d darts, so the graph is d-regular and bipartite. Left translations are
automorphisms for ANY group, so diameter is checked with 2K BFS runs from identity
representatives.

Stage A runs K = 2 (4N vertices) and Stage B runs K = 1 (2N vertices) with the
remaining time. The best valid graph wins, and the K_{d,d} fallback is always kept.
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
#define PERN 4
#define MAXCAND (PERN * MAXN)

typedef struct { int type, q, p, kf, c, m, k, r, N; } Cand;

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

/* ------------------------------------------------------------ group families */

/* gtype 0: F_q x| H, H cyclic of order GC_ (element (a, j) coded a*GC_ + j).
 * gtype 1: Z_MM x| Z_MK with r^MK = 1 mod MM (element (a, b) coded a*MK + b). */
static int gtype = 0;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int GC_ = 1;
static int MM = 1, MK = 1, MPW[MAXN];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 0;
    GN = q * c;
    GC_ = c;
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

static void setup_meta(int m, int k, int r) {
    gtype = 1;
    MM = m;
    MK = k;
    GN = m * k;
    MPW[0] = 1 % m;
    for (int b = 1; b < k; b++) MPW[b] = (int)(((long)MPW[b - 1] * r) % m);
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GC_, j = x % GC_, b = y / GC_, t = y % GC_;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC_ + HM[j * GC_ + t];
    }
    int a = x / MK, b = x % MK, c = y / MK, e = y % MK;
    int na = (int)((a + (long)MPW[b] * c) % MM);
    int nb = (b + e) % MK;
    return na * MK + nb;
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / GC_, j = x % GC_;
        int jn = (GC_ - j) % GC_;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC_ + jn;
    }
    int a = x / MK, b = x % MK;
    int nb = (MK - b) % MK;
    int na = (int)((MM - ((long)MPW[nb] * a) % MM) % MM);
    return na * MK + nb;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int cand_count = 0;
static int gfirst[MAXCAND], gcnt[MAXCAND], ng = 0;

/* For each order N (ascending), add up to PERN groups: affine F_q x| C_c first,
 * then metacyclic Z_m x| Z_k with a random starting r. */
static void gen_candidates(int lo, int hi) {
    for (int N = lo; N <= hi && cand_count < MAXCAND; N++) {
        int per = 0;
        for (int q = 3; q < MAXQ && per < PERN && cand_count < MAXCAND; q++) {
            int p, kf;
            if (N % q) continue;
            if (!factor_pp(q, &p, &kf)) continue;
            int c = N / q;
            if (c < 2 || c > q - 1 || (q - 1) % c) continue;
            Cand cd;
            memset(&cd, 0, sizeof cd);
            cd.type = 0; cd.q = q; cd.p = p; cd.kf = kf; cd.c = c; cd.N = N;
            cand[cand_count++] = cd;
            per++;
        }
        for (int k = 2; k <= N / 3 && per < PERN && cand_count < MAXCAND; k++) {
            if (N % k) continue;
            int m = N / k;
            if (m < 3) continue;
            int r0 = 1 + rndint(m - 1);
            for (int t = 0; t < m - 1 && per < PERN && cand_count < MAXCAND; t++) {
                int r = 1 + (r0 - 1 + t) % (m - 1);
                if (gcd_int(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.type = 1; cd.m = m; cd.k = k; cd.r = r; cd.N = N;
                cand[cand_count++] = cd;
                per++;
            }
        }
    }
    for (int i = 0; i < cand_count; i++) {
        if (i == 0 || cand[i].N != cand[i - 1].N) { gfirst[ng] = i; gcnt[ng] = 0; ng++; }
        gcnt[ng - 1]++;
    }
}

static void apply_cand(int i) {
    Cand *c = &cand[i];
    if (c->type == 0) setup_affine(c->q, c->p, c->kf, c->c);
    else setup_meta(c->m, c->k, c->r);
}

/* ------------------------------------------------------------ voltage lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static int bestCi = -1;
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

/* Left translations act transitively on each orbit, so one BFS per orbit suffices. */
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

/* Try every candidate group of one order within `until`; returns candidate index or -1. */
static int try_group(int g, double until) {
    int first = gfirst[g], cnt = gcnt[g];
    for (int j = 0; j < cnt; j++) {
        double rem = until - now();
        if (rem < 0.2) break;
        double slice = rem / (double)(cnt - j);
        apply_cand(first + j);
        if (search_group(now() + slice)) {
            save_best();
            bestCi = first + j;
            return first + j;
        }
        if (now() >= t_end) break;
    }
    return -1;
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

    gen_candidates(lo, hi);
    if (ng == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 1: binary search over group orders (candidates grouped by order). */
    int best_g = -1;
    int lg = 0, hg = ng - 1;
    while (lg <= hg && now() < t_end) {
        int mid = (lg + hg) / 2;
        double rem = t_end - now();
        double slice = rem * 0.25;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_group(mid, now() + slice) >= 0) {
            best_g = mid;
            lg = mid + 1;
        } else {
            hg = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next orders above the best. */
    int fails = 0;
    int g = best_g < 0 ? 0 : best_g + 1;
    while (g < ng && now() < t_end && fails < 2) {
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        if (try_group(g, now() + slice) >= 0) {
            best_g = g;
            fails = 0;
        } else {
            fails++;
        }
        g++;
    }

    if (bestCi < 0) {
        printf("0 0\n");
        return 0;
    }
    apply_cand(bestCi);
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
    """Run the C engine with K left and K right orbits over affine and metacyclic groups."""
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

        # Stage A: two-orbit lifts, 4N vertices, group order N in [best/4, mb/4].
        budget = 0.5 * left() - 2.0
        lo = max(best[0] // 4 + 1, 2)
        hi = mb // 4
        if budget > 2.0 and lo <= hi:
            try:
                consider(_orbit_lift_search(d, D, seed, budget, lo, hi, 2))
            except Exception:
                pass

        # Stage B: single-orbit lifts (2N vertices) with the remaining time.
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
