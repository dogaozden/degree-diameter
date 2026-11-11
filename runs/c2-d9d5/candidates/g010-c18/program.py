"""Mixed-group voltage lift search for the bipartite degree-diameter problem.

Bold change in this version: the C engine no longer searches only affine groups
F_q x| Z_c with two orbits. It searches a wider family:

  * affine groups F_q x| Z_c (c | q-1, c >= 1), and
  * semidirect products Z_m x| Z_k with r^k = 1 mod m (nonabelian when r != 1),

with K = 1..3 left orbits and K right orbits, so the graph has 2K|G| vertices and is
d-regular. Left translation is an automorphism of every lift, so each orbit is
transitive and the diameter check needs only 2K BFS runs.

Stage 1 reruns the proven single-orbit affine family as a safety net. Stage 2 searches
the mixed family for totals above the best graph so far. Every returned graph is
re-checked with lib.is_valid, and the fallback K_{d,d} (or the projective/Araujo-Lopez
graph) is kept if nothing better validates.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Mixed-group voltage lift search.
 * Usage: prog d D seed time_limit lo hi kmin kmax types
 *   lo, hi  : window for the total vertex count 2*K*|G|
 *   kmin..kmax : number of orbits per side (1..3)
 *   types   : bit 1 = affine F_q x| Z_c, bit 2 = semidirect Z_m x| Z_k
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 * Vertices: left L^a_x = a*GN + x (a < K); right R^b_y = K*GN + b*GN + y.
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
#define MAXK 3
#define MAXND (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 200000

typedef struct { int K, type, N, a, b, c, T; } Cand;

static int K, d, D, GN, nd;
static double t_end;
static uint64_t rs = 88172645463325252ULL;
static Cand cand[MAXCAND];
static int nc = 0;

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

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
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

/* ------------------------------------------------------------ groups */

static int GT = 0;                       /* 0 = affine, 1 = semidirect */
static int GC_ = 1;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM = 1, SK = 1, SR = 1;
static int SPW[MAXN];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GT = 0;
    GC_ = c;
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

static void setup_semi(int m, int k, int r) {
    GT = 1;
    SM = m;
    SK = k;
    SR = r;
    GN = m * k;
    GC_ = 1;
    SPW[0] = 1 % m;
    for (int b = 1; b < k; b++) SPW[b] = (int)((long)SPW[b - 1] * r % m);
}

/* Element coding: affine (a, h_j) -> a*c + j; semidirect (a, b) -> a*k + b. */
static inline int gmul(int x, int y) {
    if (GT == 0) {
        int a = x / GC_, j = x % GC_, b = y / GC_, t = y % GC_;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC_ + HM[j * GC_ + t];
    } else {
        int a = x / SK, b = x % SK, c2 = y / SK, dd = y % SK;
        int na = (int)(((long)a + (long)SPW[b] * c2) % SM);
        return na * SK + (b + dd) % SK;
    }
}
static inline int ginv(int x) {
    if (GT == 0) {
        int a = x / GC_, j = x % GC_;
        int jn = (GC_ - j) % GC_;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC_ + jn;
    } else {
        int a = x / SK, b = x % SK;
        int nb = (SK - b) % SK;
        int na = (int)((SM - (long)SPW[nb] * a % SM) % SM);
        return na * SK + nb;
    }
}

/* ------------------------------------------------------------ lift state */

static int tb[MAXND], vg[MAXND];
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN];
static int inc_t[MAXK][MAXD];
static int cnt_in[MAXK];
static int bestTb[MAXND], bestVg[MAXND];
static Cand bestCand;
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

/* Left translations are automorphisms, transitive on each orbit: one BFS per
 * orbit representative decides the diameter. */
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

static void setup_cand(const Cand *cd) {
    K = cd->K;
    nd = K * d;
    if (cd->type == 0) {
        int p, kk;
        factor_pp(cd->a, &p, &kk);
        setup_affine(cd->a, p, kk, cd->b);
    } else {
        setup_semi(cd->a, cd->b, cd->c);
    }
}

static int try_cand(const Cand *cd, double until) {
    setup_cand(cd);
    if (!search_group(until)) return 0;
    save_best();
    bestCand = *cd;
    return 1;
}

static int cmp_cand(const void *pa, const void *pb) {
    const Cand *a = pa, *b = pb;
    if (a->T != b->T) return a->T < b->T ? -1 : 1;
    if (a->K != b->K) return a->K - b->K;
    if (a->type != b->type) return a->type - b->type;
    if (a->N != b->N) return a->N - b->N;
    if (a->a != b->a) return a->a - b->a;
    if (a->b != b->b) return a->b - b->b;
    return a->c - b->c;
}

static void add_cand(int KK, int type, int N, int a, int b, int c) {
    if (nc >= MAXCAND) return;
    Cand cd;
    cd.K = KK;
    cd.type = type;
    cd.N = N;
    cd.a = a;
    cd.b = b;
    cd.c = c;
    cd.T = 2 * KK * N;
    cand[nc++] = cd;
}

static void gen_cands(int lo, int hi, int kmin, int kmax, int types) {
    nc = 0;
    for (int KK = kmin; KK <= kmax; KK++) {
        long per = 2L * KK;
        long Nlo = (lo + per - 1) / per;
        long Nhi = hi / per;
        if (Nlo < 2) Nlo = 2;
        if (Nhi > MAXN) Nhi = MAXN;
        if (Nlo > Nhi) continue;
        if (types & 1) {
            for (int q = 3; q < MAXQ; q++) {
                int p, kk;
                if (!factor_pp(q, &p, &kk)) continue;
                for (int c = 1; c <= q - 1; c++) {
                    if ((q - 1) % c) continue;
                    long N = (long)q * c;
                    if (N >= Nlo && N <= Nhi) add_cand(KK, 0, (int)N, q, c, 0);
                }
            }
        }
        if (types & 2) {
            for (long N = Nlo; N <= Nhi; N++) {
                for (long m = 2; m <= N; m++) {
                    if (N % m) continue;
                    int k = (int)(N / m);
                    add_cand(KK, 1, (int)N, (int)m, k, 1);
                    if (m >= 3 && k >= 2) {
                        int got = 0;
                        for (int tries = 0; tries < 8 && got < 2; tries++) {
                            int r = 2 + rndint((int)m - 2);
                            if (gcd_l(r, m) == 1 && powmod_l(r, k, m) == 1) {
                                add_cand(KK, 1, (int)N, (int)m, k, r);
                                got++;
                            }
                        }
                    }
                }
            }
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 10) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    int kmin = atoi(argv[7]), kmax = atoi(argv[8]);
    int types = atoi(argv[9]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (kmin < 1) kmin = 1;
    if (kmax > MAXK) kmax = MAXK;
    if (kmin > kmax || types < 1 || types > 3) {
        printf("0 0\n");
        return 0;
    }
    if (lo < 2) lo = 2;

    gen_cands(lo, hi, kmin, kmax, types);
    if (nc == 0) {
        printf("0 0\n");
        return 0;
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    double total = t_end - t0;
    double cap = 0.2 * total;
    if (cap < 0.5) cap = 0.5;

    /* Phase 1: binary search over candidates sorted by total vertex count. */
    int best_idx = -1;
    int li = 0, hi_i = nc - 1;
    while (li <= hi_i && now() < t_end) {
        int mid = (li + hi_i) / 2;
        double rem = t_end - now();
        double slice = 0.25 * rem;
        if (slice > cap) slice = cap;
        if (slice < 0.3) slice = 0.3;
        if (slice > rem) slice = rem;
        if (try_cand(&cand[mid], now() + slice)) {
            best_idx = mid;
            li = mid + 1;
        } else {
            hi_i = mid - 1;
        }
    }

    /* Phase 2: climb through larger totals with the remaining time. A failed
     * total skips the other groups with the same total. */
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    int fails = 0, failT = -1;
    while (idx < nc && now() < t_end && fails < 6) {
        const Cand *cd = &cand[idx];
        if (best_idx >= 0 && cd->T <= cand[best_idx].T) { idx++; continue; }
        if (cd->T == failT) { idx++; continue; }
        double rem = t_end - now();
        double slice = cap < rem ? cap : rem;
        if (try_cand(cd, now() + slice)) {
            best_idx = idx;
            fails = 0;
            failT = -1;
        } else {
            fails++;
            failT = cd->T;
        }
        idx++;
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_cand(&bestCand);
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


def _mixed_lift_search(d, D, seed, budget, lo, hi, kmin, kmax, types):
    """Run the C engine on total vertex window [lo, hi]; returns (n, edges), possibly (0, [])."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, kmin, kmax, types],
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
        lo = best[0] + 1
        hi = mb
        if lo <= hi:
            # Stage 1: safety net, the proven single-orbit affine family.
            budget = 0.4 * (left() - 12)
            if budget > 3:
                try:
                    consider(_mixed_lift_search(d, D, seed, budget, lo, hi, 1, 1, 1))
                except Exception:
                    pass

            # Stage 2 (bold): mixed affine + semidirect groups with K = 1..3 orbits,
            # restricted to totals strictly above the best graph found so far.
            budget = left() - 14
            lo2 = max(lo, best[0] + 1)
            if budget > 3 and lo2 <= hi:
                try:
                    consider(_mixed_lift_search(d, D, seed + 1, budget, lo2, hi, 1, 3, 3))
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
