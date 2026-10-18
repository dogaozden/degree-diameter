"""Combined two-orbit affine voltage lifts for the bipartite degree-diameter problem.

Merges the two parents:
  * general dart-to-orbit assignment with B = 1 or 2 orbits per side (parent 1's
    balanced target swaps, parent 2's B = 2 pattern family is a special case);
  * voltage lifts over F_q x| H (affine groups), with exp/log field tables so that
    large prime-power fields are reachable without q x q tables;
  * duplicate darts penalised heavily, so accepted states are simple graphs;
  * cover check from the 2B orbit representatives (left translations are
    automorphisms that are transitive on each orbit);
  * ascending scan over group orders: easy orders are found quickly, and the scan
    stops after a few consecutive failures, so time moves to the next family;
  * final full BFS check from every vertex when the graph is small enough.
Python builds the classical constructions, runs the C engine once, and keeps
only graphs that pass lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit (B = 1 or 2) affine voltage lifts.
 * Group G = F_q x| H, |G| = N = q*c, c | q-1, 2 <= c < 128.
 * Left vertex (i,g) = i*N + g, right vertex (j,y) = B*N + j*N + y.
 * Dart t (left orbit t/d) has target orbit dtg[t] and voltage dvol[t]:
 *   L_(i,g) ~ R_(dtg[t], g*dvol[t]).
 * Every right orbit receives exactly d darts, so the graph is d-regular.
 * Usage: prog d D seed time_limit lo2 hi2 lo1 hi1
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQF 2400
#define MAXC 128
#define MAXN 4800
#define MAXD 32
#define MAXB 2
#define MAXND (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 20000
#define DUP_PEN 1000000L

typedef struct { int q, p, k, c, N; } Cand;

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

static int fq_, fp_, fk_;
static int fpw[17];
static int fmodc[16];          /* x^k = -sum fmodc[i] x^i for k >= 2 */
static int fready = 0;
static int EXPT[MAXQF], LOGT[MAXQF];

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

/* Product in Z_p[x]/(f) for the field under construction. */
static int fmulp(int a, int b) {
    if (fk_ == 1) return (a * b) % fp_;
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < fk_; i++) {
        pa[i] = (a / fpw[i]) % fp_;
        pb[i] = (b / fpw[i]) % fp_;
    }
    for (int i = 0; i < 2 * fk_; i++) prod[i] = 0;
    for (int i = 0; i < fk_; i++)
        for (int j = 0; j < fk_; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % fp_;
    for (int deg = 2 * fk_ - 2; deg >= fk_; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < fk_; i++) {
            int idx = deg - fk_ + i;
            prod[idx] = ((prod[idx] - c * fmodc[i]) % fp_ + fp_) % fp_;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < fk_; i++) r += prod[i] * fpw[i];
    return r;
}

/* x generates the multiplicative group iff its order is exactly q-1. */
static int try_gen(int x) {
    int cur = 1;
    EXPT[0] = 1;
    for (int i = 1; i < fq_ - 1; i++) {
        cur = fmulp(cur, x);
        if (cur == 0 || cur == 1) return 0;
        EXPT[i] = cur;
    }
    if (fmulp(cur, x) != 1) return 0;
    for (int i = 0; i < fq_ - 1; i++) LOGT[EXPT[i]] = i;
    return 1;
}

static void setup_field(int q) {
    if (fready && fq_ == q) return;
    int p, k;
    fready = 0;
    if (!factor_pp(q, &p, &k)) return;
    fq_ = q;
    fp_ = p;
    fk_ = k;
    fpw[0] = 1;
    for (int i = 1; i <= k; i++) fpw[i] = fpw[i - 1] * p;
    int ok = 0;
    if (k == 1) {
        for (int g = 2; g < q && !ok; g++) ok = try_gen(g);
    } else {
        for (int code = 0; code < q && !ok; code++) {
            int t = code;
            for (int i = 0; i < k; i++) { fmodc[i] = t % p; t /= p; }
            ok = try_gen(p);   /* the polynomial x */
        }
    }
    fready = ok;
}

static inline int fadd(int a, int b) {
    if (fk_ == 1) {
        int s = a + b;
        if (s >= fq_) s -= fq_;
        return s;
    }
    int r = 0;
    for (int i = 0; i < fk_; i++) {
        int s = (a % fp_ + b % fp_) % fp_;
        r += s * fpw[i];
        a /= fp_;
        b /= fp_;
    }
    return r;
}

static inline int fneg(int a) {
    if (fk_ == 1) return a ? fq_ - a : 0;
    int r = 0;
    for (int i = 0; i < fk_; i++) {
        int s = (fp_ - a % fp_) % fp_;
        r += s * fpw[i];
        a /= fp_;
    }
    return r;
}

static inline int fmul(int a, int b) {
    if (!a || !b) return 0;
    int s = LOGT[a] + LOGT[b];
    if (s >= fq_ - 1) s -= fq_ - 1;
    return EXPT[s];
}

/* ------------------------------------------------------------ group G = F_q x| H */

static int GC, GN, GQ;
static int Hel[MAXC], hidx[MAXQF], HM[MAXC * MAXC];

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c). */
static void setup_group(int c) {
    GC = c;
    GQ = fq_;
    GN = fq_ * c;
    int step = (fq_ - 1) / c;
    for (int v = 0; v < fq_; v++) hidx[v] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = EXPT[(t * step) % (fq_ - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[fmul(Hel[j], Hel[t])];
}

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = fadd(a, fmul(Hel[j], b));
    return na * GC + HM[j * GC + t];
}

static inline int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = fneg(fmul(Hel[jn], a));
    return na * GC + jn;
}

/* ------------------------------------------------------------ lift state */

static int B_cur = 1, nd = 0;
static int dtg[MAXND], dvol[MAXND];
static int fw[MAXND][MAXN], bw[MAXND][MAXN];
static int inc[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int ADJ[MAXV][MAXD];

static void rebuild_inc(void) {
    int cnt[MAXB];
    for (int j = 0; j < B_cur; j++) cnt[j] = 0;
    for (int t = 0; t < nd; t++) {
        int j = dtg[t];
        if (cnt[j] < d) inc[j][cnt[j]++] = t;
    }
}

/* Dart t: L_g ~ R_(g x), so right y has neighbour y x^-1 through the same dart. */
static void set_dart(int t, int x) {
    dvol[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

static int dup_count(void) {
    int c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && dtg[t1] == dtg[t2] && dvol[t1] == dvol[t2]) c++;
    return c;
}

static void random_init(void) {
    int list[MAXND], p = 0;
    for (int j = 0; j < B_cur; j++)
        for (int k = 0; k < d; k++) list[p++] = j;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i];
        list[i] = list[j];
        list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) dtg[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) {
        int x = rndint(GN);
        for (int tries = 0; tries < 200; tries++) {
            int clash = 0;
            for (int t2 = (t / d) * d; t2 < t; t2++)
                if (dtg[t2] == dtg[t] && dvol[t2] == x) { clash = 1; break; }
            if (!clash) break;
            x = rndint(GN);
        }
        set_dart(t, x);
    }
}

/* Vertices reached from src within distance D. */
static int bfs_count(int src) {
    int N = GN, BN = B_cur * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int tt = 0; tt < d; tt++) {
                    int t = i * d + tt;
                    int u = BN + dtg[t] * N + fw[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int t = inc[j][k];
                    int u = (t / d) * N + bw[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the 2B orbit representatives, plus a heavy duplicate penalty. */
static long full_cost(void) {
    long V = 2L * B_cur * GN;
    long BNv = (long)B_cur * GN;
    long c = 0;
    for (int i = 0; i < B_cur; i++) c += V - bfs_count(i * GN);
    for (int j = 0; j < B_cur; j++) c += V - bfs_count((int)BNv + j * GN);
    return c + DUP_PEN * (long)dup_count();
}

/* Simulated annealing over voltages and target swaps; returns 1 on cost 0. */
static int search_group(double until) {
    const int iters = 8000;
    while (now() < until) {
        random_init();
        long cost = full_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (B_cur > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (dtg[t1] == dtg[t2]) continue;
                int tmp = dtg[t1];
                dtg[t1] = dtg[t2];
                dtg[t2] = tmp;
                rebuild_inc();
                long c2 = full_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = dtg[t1];
                    dtg[t1] = dtg[t2];
                    dtg[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd), x = rndint(GN);
                if (x == dvol[t]) continue;
                int old = dvol[t];
                set_dart(t, x);
                long c2 = full_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best record */

static int best_total = 0, best_B = 0, best_N = 0;
static int best_q = 0, best_p = 0, best_k = 0, best_c = 0;
static int best_dtg[MAXND], best_dvol[MAXND];

static void record_best(void) {
    int total = 2 * B_cur * GN;
    if (total <= best_total) return;
    best_total = total;
    best_B = B_cur;
    best_N = GN;
    best_q = fq_;
    best_p = fp_;
    best_k = fk_;
    best_c = GC;
    for (int t = 0; t < nd; t++) {
        best_dtg[t] = dtg[t];
        best_dvol[t] = dvol[t];
    }
}

/* ------------------------------------------------------------ candidates and scan */

static Cand cand[MAXCAND];
static int nc = 0;

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q < MAXQF; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c < q && c < MAXC; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) {
            cand[j + 1] = cand[j];
            j--;
        }
        cand[j + 1] = t;
    }
}

/* Ascending scan over orders in [lo, hi]. Stops after a few consecutive failures,
 * so feasibility is found quickly when it exists and time is not wasted. */
static void scan_phase(int Bv, int lo, int hi, double until) {
    if (lo > hi || now() >= until) return;
    build_cands(lo, hi);
    B_cur = Bv;
    nd = Bv * d;
    double len = until - now();
    int fails = 0;
    for (int idx = 0; idx < nc && now() < until && fails < 4; idx++) {
        if (2L * Bv * cand[idx].N <= (long)best_total) continue;
        double rem = until - now();
        double slice = 0.15 * len;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        setup_field(cand[idx].q);
        if (!fready) continue;
        setup_group(cand[idx].c);
        B_cur = Bv;
        nd = Bv * d;
        if (search_group(now() + slice)) {
            record_best();
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

static int ADJ_dummy = 0;

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo2 = atoi(argv[5]), hi2 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.95 - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    (void)ADJ_dummy;

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    int hmax = MAXN - 1;
    if (hi2 > hmax) hi2 = hmax;
    if (hi1 > hmax) hi1 = hmax;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;

    double span = t_end - t0;

    /* Phase 1: two-orbit family (4N vertices). */
    scan_phase(2, lo2, hi2, t0 + 0.40 * span);

    /* Phase 2: single-orbit family (2N vertices), only orders beating the best. */
    int l1 = lo1;
    if (best_total / 2 + 1 > l1) l1 = best_total / 2 + 1;
    scan_phase(1, l1, hi1, t0 + 0.75 * span);

    /* Phase 3: continue the family that currently holds the best graph. */
    if (best_B == 2) scan_phase(2, best_N + 1, hi2, t_end);
    else if (best_B == 1) scan_phase(1, best_N + 1, hi1, t_end);

    if (best_total == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_field(best_q);
    setup_group(best_c);
    B_cur = best_B;
    nd = B_cur * d;
    for (int t = 0; t < nd; t++) dtg[t] = best_dtg[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, best_dvol[t]);

    int N = GN, BN = B_cur * N, V = 2 * BN;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int tt = 0; tt < d; tt++) {
            int t = i * d + tt;
            ADJ[v][tt] = BN + dtg[t] * N + fw[t][g];
        }
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, y = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int t = inc[j][k];
            ADJ[w][k] = (t / d) * N + bw[t][y];
        }
    }

    /* Full check from every vertex when cheap. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = ADJ[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, BN * d);
    for (int v = 0; v < BN; v++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", v, ADJ[v][k]);
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

    # Combined search: two-orbit (4N vertices) and single-orbit (2N vertices) lifts.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.5
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        if budget > 2.0 and (lo2 <= hi2 or lo1 <= hi1):
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo2, hi2, lo1, hi1],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
