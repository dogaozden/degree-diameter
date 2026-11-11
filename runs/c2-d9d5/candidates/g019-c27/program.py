"""Multi-fiber affine voltage lifts for the bipartite degree-diameter problem.

Change from the parent: the C engine no longer searches only single-pair Haar graphs.
It searches voltage lifts with t fibers per side (t = 1, 2, 3) over the affine group
G = F_q x| H, where H is the subgroup of F_q^* of order c dividing q-1.

Base graph: t A-fibers and t B-fibers joined by d*t darts. Layer l gives a permutation
sigma_l of {0..t-1}, and dart (l, u) joins A-fiber u to B-fiber sigma_l(u) with a group
voltage s. Every fiber then has degree exactly d. Darts with the same endpoints need
distinct voltages, so the lift is simple. The lift is bipartite by construction.

Left translation by G is an automorphism of the lift and moves each fiber transitively.
So the diameter test needs only 2t BFS runs, one from the identity of each fiber. Total
order is 2 t |G|.

Moves: change one dart voltage, or swap two targets within one layer. Search is iterated
annealing from the incumbent, as in the parent. Every output is re-checked in Python,
and the Haar graph K_{d,d} plus the projective-plane and generalized-quadrangle
constructions remain the fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-fiber affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi
 *   lo, hi bound the TOTAL vertex count 2*t*|G|.
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
#define MAXN 4096
#define MAXT 3
#define MAXD 32
#define MAXTD (MAXT * MAXD)
#define MAXV (2 * MAXT * MAXN)
#define MAXCAND 16384
#define ITERS 6000

typedef struct { int q, p, k, c, t, N, total; } Cand;
typedef struct { int type, k1, k2, oldv; } Move;

static int d, D, T, TD, GN, GC, GQ;
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

/* ------------------------------------------------------------ group F_q x| H */

static int Hel[MAXQ], hidx[MAXQ], HM[MAXQ * MAXQ], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, h_j = g^(j*(q-1)/c).
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). Identity is code 0. */
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

/* ------------------------------------------------------------ lift state */

/* Dart index k = l*T + u: A-fiber u joined to B-fiber dv[k] with voltage vs[k].
 * Fiber u of dart k is k % T. Column sums are d because each layer is a permutation. */
static int dv[MAXTD], vs[MAXTD];
static int fwd[MAXTD][MAXN], bwd[MAXTD][MAXN];
static int lb[MAXT][MAXD];
static int bdv[MAXTD], bvs[MAXTD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* A(u,g) ~ B(v, g*s); B(v,h) ~ A(u, h*s^-1). */
static void set_dart(int k) {
    int inv = ginv(vs[k]);
    for (int g = 0; g < GN; g++) {
        fwd[k][g] = gmul(g, vs[k]);
        bwd[k][g] = gmul(g, inv);
    }
}

static void rebuild_lists(void) {
    for (int v = 0; v < T; v++) {
        int cnt = 0;
        for (int k = 0; k < TD; k++)
            if (dv[k] == v && cnt < d) lb[v][cnt++] = k;
    }
}

static int simple_ok_dart(int k) {
    for (int j = 0; j < TD; j++)
        if (j != k && j % T == k % T && dv[j] == dv[k] && vs[j] == vs[k]) return 0;
    return 1;
}

/* Vertices: A(u,g) = u*GN + g, B(v,h) = (T+v)*GN + h. */
static int bfs_count(int src) {
    int N = GN;
    int AB = T * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int x = que[head++];
            if (x < AB) {
                int u = x / N, g = x - u * N;
                for (int l = 0; l < d; l++) {
                    int k = l * T + u;
                    int y = AB + dv[k] * N + fwd[k][g];
                    if (vis[y] != stamp_) { vis[y] = stamp_; que[tail++] = y; }
                }
            } else {
                int r = x - AB;
                int v = r / N, h = r - v * N;
                for (int i = 0; i < d; i++) {
                    int k = lb[v][i];
                    int u = k % T;
                    int y = u * N + bwd[k][h];
                    if (vis[y] != stamp_) { vis[y] = stamp_; que[tail++] = y; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms that move each fiber transitively, so one BFS
 * per fiber (from its identity vertex) decides the diameter. */
static long cost_all(void) {
    long V = 2L * T * GN, c = 0;
    for (int u = 0; u < T; u++) {
        c += V - bfs_count(u * GN);
        c += V - bfs_count((T + u) * GN);
    }
    return c;
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXT];
        for (int u = 0; u < T; u++) perm[u] = u;
        for (int u = T - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int tmp = perm[u]; perm[u] = perm[j]; perm[j] = tmp;
        }
        for (int u = 0; u < T; u++) dv[l * T + u] = perm[u];
    }
    for (int k = 0; k < TD; k++) vs[k] = rndint(GN);
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int k = 0; k < TD; k++)
            if (!simple_ok_dart(k)) { vs[k] = rndint(GN); changed = 1; }
    }
    for (int k = 0; k < TD; k++) set_dart(k);
    rebuild_lists();
}

/* Apply a random valid move. Returns 0 (state unchanged) if the move breaks simplicity. */
static int apply_move(Move *mv) {
    if (T == 1 || (rnd() & 1)) {
        int k = rndint(TD), x = rndint(GN);
        if (x == vs[k]) return 0;
        int old = vs[k];
        vs[k] = x;
        if (!simple_ok_dart(k)) { vs[k] = old; return 0; }
        set_dart(k);
        mv->type = 0; mv->k1 = k; mv->k2 = -1; mv->oldv = old;
        return 1;
    }
    int l = rndint(d), u1 = rndint(T), u2 = rndint(T);
    if (u1 == u2) return 0;
    int k1 = l * T + u1, k2 = l * T + u2;
    int tmp = dv[k1]; dv[k1] = dv[k2]; dv[k2] = tmp;
    if (!simple_ok_dart(k1) || !simple_ok_dart(k2)) {
        tmp = dv[k1]; dv[k1] = dv[k2]; dv[k2] = tmp;
        return 0;
    }
    rebuild_lists();
    mv->type = 1; mv->k1 = k1; mv->k2 = k2; mv->oldv = 0;
    return 1;
}

static void undo_move(const Move *mv) {
    if (mv->type == 0) {
        vs[mv->k1] = mv->oldv;
        set_dart(mv->k1);
    } else {
        int tmp = dv[mv->k1]; dv[mv->k1] = dv[mv->k2]; dv[mv->k2] = tmp;
        rebuild_lists();
    }
}

/* Iterated annealing. The first round starts from a random configuration. Later rounds
 * perturb the incumbent with two moves and anneal from a lower starting temperature.
 * Returns 1 with the state left at a cost-0 configuration, or 0 on timeout. */
static int search_cfg(double until) {
    int have = 0;
    long bestc = 0;
    int incdv[MAXTD], incvs[MAXTD];
    while (now() < until) {
        if (!have) {
            randomize();
        } else {
            memcpy(dv, incdv, sizeof(int) * (size_t)TD);
            memcpy(vs, incvs, sizeof(int) * (size_t)TD);
            for (int k = 0; k < TD; k++) set_dart(k);
            rebuild_lists();
            for (int t2 = 0; t2 < 2; t2++) {
                Move mv;
                int tries = 0;
                while (!apply_move(&mv) && tries++ < 50) {}
            }
        }
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double Tm = Ts * pow(Te / Ts, (double)it / ITERS);
            Move mv;
            if (!apply_move(&mv)) continue;
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / Tm)) {
                cost = c2;
            } else {
                undo_move(&mv);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incdv, dv, sizeof(int) * (size_t)TD);
            memcpy(incvs, vs, sizeof(int) * (size_t)TD);
        }
    }
    return 0;
}

static void print_result(void) {
    int N = GN;
    printf("%d %d\n", 2 * T * N, T * d * N);
    for (int k = 0; k < TD; k++) {
        int u = k % T;
        for (int g = 0; g < N; g++)
            printf("%d %d\n", u * N + g, (T + dv[k]) * N + fwd[k][g]);
    }
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    return (x->total > y->total) - (x->total < y->total);
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

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < 2L * d || N > MAXN) continue;
            for (int t = 1; t <= MAXT; t++) {
                long total = 2L * t * N;
                if (total < lo || total > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, t, (int)N, (int)total};
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Ascending by total order: each attempt gets 20% of the remaining time (at least
     * 1 s). Only candidates strictly larger than the best found so far are tried. */
    long bestTotal = 0;
    int bestci = -1;
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        if (cand[ci].total <= bestTotal) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cand[ci].q, cand[ci].p, cand[ci].k, cand[ci].c);
        T = cand[ci].t;
        TD = T * d;
        if (search_cfg(now() + slice)) {
            bestTotal = cand[ci].total;
            bestci = ci;
            memcpy(bdv, dv, sizeof(int) * (size_t)TD);
            memcpy(bvs, vs, sizeof(int) * (size_t)TD);
        }
    }

    if (bestci < 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(cand[bestci].q, cand[bestci].p, cand[bestci].k, cand[bestci].c);
    T = cand[bestci].t;
    TD = T * d;
    memcpy(dv, bdv, sizeof(int) * (size_t)TD);
    memcpy(vs, bvs, sizeof(int) * (size_t)TD);
    for (int k = 0; k < TD; k++) set_dart(k);
    rebuild_lists();
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

    # Search: multi-fiber affine voltage lifts. Totals below the current best are useless,
    # so the window starts just above it (but no lower than Moore/8 to keep orders large).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 8)
        hi = mb
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 4.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
