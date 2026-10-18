"""Combined multi-orbit affine lifts for the bipartite degree-diameter problem.

Merges two parent ideas:
  * multi-orbit lifts with B in {1, 2, 3} left and right orbits over G = F_q x| H
    (parent g006-c09), with BFS cover checks from the 2B orbit representatives;
  * dart-target swap moves that keep each right orbit at exactly d darts, plus a
    duplicate-dart penalty (parent g005-c24).

Group orders are N = q*c with c | q-1, including c = 1 (plain F_q translations).
The C engine searches B = 3 (6N vertices) first, then B = 1 (2N), then B = 2 (4N),
each with a binary search over N and an upward sweep. Lower bounds come from the
best graph already in hand, so only strict improvements are searched. The C engine
checks simplicity and, for V <= 6000, a full BFS from every vertex before printing.
Python re-checks everything with lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit affine voltage lifts over G = F_q x| H, B in {1,2,3} orbits per side.
 * Usage: prog d D seed time_limit lo3 hi3 lo1 hi1 lo2 hi2
 * Output: "n m" then m lines "u v", or "0 0".
 * Vertices: left L^a_x = a*GN + x, right R^b_y = B*GN + b*GN + y.
 * Dart t = a*d + i leaves left orbit a: L^a_x ~ R^{tb[t]}_{x * vg[t]}.
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
#define MAXB 3
#define MAXND (MAXB * MAXD)
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 16384

typedef struct { int q, p, k, c, N; } Cand;

static int d, D, B, nd, GN, GC_;
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

static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
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

static inline int gmul(int x, int y) {
    int a = x / GC_, j = x % GC_, b = y / GC_, t = y % GC_;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC_ + HM[j * GC_ + t];
}

static int ginv(int x) {
    int a = x / GC_, j = x % GC_;
    int jn = (GC_ - j) % GC_;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC_ + jn;
}

/* ------------------------------------------------------------ lift state */

static int tb[MAXND], vg[MAXND];                 /* dart target orbit, voltage */
static int fwdT[MAXND][MAXN], invT[MAXND][MAXN]; /* x*v and x*v^-1 */
static int incT[MAXB][MAXD];                     /* darts entering right orbit b */
static int bestTb[MAXND], bestVg[MAXND];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int adj[MAXV][MAXD];

static int bestTotal = 0, bestB = 0, bestQ = 0, bestP = 0, bestK = 0, bestC = 0, bestN = 0;

static void set_dart(int t, int x) {
    vg[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwdT[t][g] = gmul(g, x);
        invT[t][g] = gmul(g, xi);
    }
}

static void rebuild_inc(void) {
    int cnt[MAXB];
    for (int b = 0; b < B; b++) cnt[b] = 0;
    for (int t = 0; t < nd; t++) {
        int b = tb[t];
        incT[b][cnt[b]++] = t;
    }
}

/* Each right orbit receives exactly d darts (shuffle of a fixed multiset). */
static void random_init(void) {
    int list[MAXND], p = 0;
    for (int b = 0; b < B; b++)
        for (int i = 0; i < d; i++) list[p++] = b;
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int tmp = list[i]; list[i] = list[j]; list[j] = tmp;
    }
    for (int t = 0; t < nd; t++) tb[t] = list[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, rndint(GN));
}

/* Darts of the same left orbit with equal target and voltage give a repeated edge. */
static long dup_count(void) {
    long c = 0;
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (t1 / d == t2 / d && tb[t1] == tb[t2] && vg[t1] == vg[t2]) c++;
    return c;
}

/* Vertices reached within distance D of src. */
static int bfs_count(int src) {
    int V2 = B * GN;
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
                int w = v - V2, b = w / GN, y = w % GN;
                for (int j = 0; j < d; j++) {
                    int t = incT[b][j];
                    int u = (t / d) * GN + invT[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms transitive on each orbit, so BFS from the
 * 2B representatives decides the diameter. */
static long cover_cost(void) {
    long V = 2L * B * GN, c = 0;
    for (int a = 0; a < B; a++) c += V - bfs_count(a * GN);
    for (int b = 0; b < B; b++) c += V - bfs_count(B * GN + b * GN);
    return c + 1000L * dup_count();
}

/* Simulated annealing; moves are target swaps (B > 1) and voltage changes.
 * Returns 1 with a cost-0 state in tb/vg, 0 on timeout. */
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
            if (B > 1 && rnd01() < 0.4) {
                int t1 = rndint(nd), t2 = rndint(nd);
                if (tb[t1] == tb[t2]) continue;
                int tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                rebuild_inc();
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                    cost = c2;
                } else {
                    tmp = tb[t1]; tb[t1] = tb[t2]; tb[t2] = tmp;
                    rebuild_inc();
                }
            } else {
                int t = rndint(nd), x = rndint(GN);
                if (x == vg[t]) continue;
                int old = vg[t];
                set_dart(t, x);
                long c2 = cover_cost();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static Cand cand[MAXCAND];
static int nc = 0;

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                cand[nc].q = q;
                cand[nc].p = p;
                cand[nc].k = k;
                cand[nc].c = c;
                cand[nc].N = (int)N;
                nc++;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

static void record(int Bv, Cand cd) {
    int total = 2 * Bv * cd.N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = Bv;
    bestN = cd.N;
    bestQ = cd.q;
    bestP = cd.p;
    bestK = cd.k;
    bestC = cd.c;
    memcpy(bestTb, tb, sizeof(tb));
    memcpy(bestVg, vg, sizeof(vg));
}

/* Binary search over orders for a feasible N, then sweep upward. */
static void run_phase(int Bv, int lo, int hi, double until) {
    B = Bv;
    nd = B * d;
    build_cands(lo, hi);
    if (nc == 0) return;
    int a = 0, b = nc - 1, bestIdx = -1, bestNp = 0;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = 0.3 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[mid].q, cand[mid].p, cand[mid].k, cand[mid].c);
        if (search_group(now() + slice)) {
            record(Bv, cand[mid]);
            if (cand[mid].N > bestNp) { bestNp = cand[mid].N; bestIdx = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    int fails = 0;
    int idx = bestIdx < 0 ? 0 : bestIdx + 1;
    while (idx < nc && now() < until && fails < 2) {
        if (cand[idx].N <= bestNp) { idx++; continue; }
        double rem = until - now();
        double slice = 0.6 * rem;
        if (slice > rem) slice = rem;
        setup_group(cand[idx].q, cand[idx].p, cand[idx].k, cand[idx].c);
        if (search_group(now() + slice)) {
            record(Bv, cand[idx]);
            bestNp = cand[idx].N;
            bestIdx = idx;
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo3 = atoi(argv[5]), hi3 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    int lo2 = atoi(argv[9]), hi2 = atoi(argv[10]);
    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (hi3 > MAXN) hi3 = MAXN;
    if (hi1 > MAXN) hi1 = MAXN;
    if (hi2 > MAXN) hi2 = MAXN;
    if (lo3 < 2) lo3 = 2;
    if (lo1 < 2) lo1 = 2;
    if (lo2 < 2) lo2 = 2;

    double span = t_end - t0;
    if (span < 1.0) {
        printf("0 0\n");
        return 0;
    }

    /* Phase 1: three orbits per side (6N vertices). */
    if (lo3 <= hi3) run_phase(3, lo3, hi3, t0 + 0.45 * span);
    /* Phase 2: one orbit per side (2N vertices). */
    if (lo1 <= hi1) run_phase(1, lo1, hi1, t0 + 0.75 * span);
    /* Phase 3: two orbits per side (4N vertices), with whatever time is left. */
    if (lo2 <= hi2) run_phase(2, lo2, hi2, t_end);

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    B = bestB;
    nd = B * d;
    setup_group(bestQ, bestP, bestK, bestC);
    for (int t = 0; t < nd; t++) tb[t] = bestTb[t];
    rebuild_inc();
    for (int t = 0; t < nd; t++) set_dart(t, bestVg[t]);

    int BN = B * GN, V = 2 * BN, E = BN * d;
    for (int v = 0; v < BN; v++) {
        int a = v / GN, x = v % GN;
        for (int i = 0; i < d; i++) {
            int t = a * d + i;
            adj[v][i] = BN + tb[t] * GN + fwdT[t][x];
        }
    }
    for (int w = BN; w < V; w++) {
        int y = (w - BN) % GN, b = (w - BN) / GN;
        for (int j = 0; j < d; j++) {
            int t = incT[b][j];
            adj[w][j] = (t / d) * GN + invT[t][y];
        }
    }

    /* Simplicity: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) { printf("0 0\n"); return 0; }

    /* Full diameter check from every vertex when cheap. */
    if (V <= 6000) {
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
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) { printf("0 0\n"); return 0; }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", v, adj[v][k]);
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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Leave room for the one-time C compile and the Python checks.
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 3.0
        b0 = best[0]
        # Only search orders that would strictly beat the current best (2B*N > b0).
        lo3 = max(2 * d, b0 // 6 + 1, mb // 24)
        hi3 = mb // 6
        lo1 = max(2 * d, b0 // 2 + 1, mb // 8)
        hi1 = mb // 2
        lo2 = max(2 * d, b0 // 4 + 1, mb // 16)
        hi2 = mb // 4
        if budget > 4.0 and (lo3 <= hi3 or lo1 <= hi1 or lo2 <= hi2):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  lo3, hi3, lo1, hi1, lo2, hi2],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
