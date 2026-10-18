"""Bi-Cayley lift search for the bipartite degree-diameter problem.

New family: instead of one Haar graph on a group G (2|G| vertices), take a 2-class
bi-Cayley lift with K classes per side and dart-count matrix
    M = [[a, d-a], [d-a, a]]   (K = 2, 1 <= a <= d-1),
or M = [d] (K = 1, the Haar graph). Vertices are (i, g) for left classes and
(j, h) for right classes, and a dart (i, j, s) joins (i, g) to (j, g*s).
Left translation by t maps (i, g) to (i, t*g) and preserves every edge, so each
class is vertex-transitive. Diameter <= D therefore reduces to BFS runs from one
representative per class, 2K BFS runs in total.

The group is the metacyclic group Z_m x|_r Z_k with m*k = N. Its order N is the
only constraint. K = 2 lets the order be about a quarter of the vertex count, so
the search works with much smaller groups.

The C engine climbs the target vertex count V upward in steps of 2. For each V it
tries a few random (K, group, a) combinations with simulated annealing on the dart
labels, and keeps the largest V that succeeds. Build() keeps the best valid graph
among the classical constructions and the search result, and falls back to a
valid graph in every case.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley lift search over metacyclic groups.
 * Usage: prog d D seed time_limit lo_V hi_V     (stdin ignored)
 * Output: "V E" then E lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4700
#define MAXV 19000
#define MAXD 32
#define MAXDART 64
#define MAXCOMB 8192
#define MAXTRY 5
#define ITERS 5000

typedef struct { int K, m, kk, r, a; } Comb;

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

/* ------------------------------------------------------------ group Z_m x| Z_k
 * Element x = a*GK + b with a in Z_GM, b in Z_GK.
 * (a,b)(c,e) = (a + r^b c, b + e). Needs r^GK = 1 mod GM. */
static int GM, GK, GN;
static int PW[MAXN];

static void setup_group(int m, int kk, int r) {
    GM = m;
    GK = kk;
    GN = m * kk;
    PW[0] = 1 % m;
    for (int b = 1; b < kk; b++) PW[b] = (int)((long)PW[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    int na = (a + PW[b] * c) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    int na = (GM - (PW[nb] * a) % GM) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift structure */

static int KC, VN, DN;
static int BC[2][2], BST[2][2];
static int dRow[MAXDART], dCol[MAXDART], dS[MAXDART], dBS[MAXDART], dBL[MAXDART];
static int rowD[2][MAXD], colD[2][MAXD];
static int FWD[MAXDART][MAXN], BWD[MAXDART][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestS[MAXDART];
static Comb bestC;

/* Needs setup_group first (for VN). */
static void setup_structure(int kc, int a) {
    KC = kc;
    for (int i = 0; i < 2; i++)
        for (int j = 0; j < 2; j++) BC[i][j] = 0;
    if (kc == 1) {
        BC[0][0] = d;
    } else {
        BC[0][0] = a;
        BC[1][1] = a;
        BC[0][1] = d - a;
        BC[1][0] = d - a;
    }
    DN = 0;
    int rc[2] = {0, 0}, cc[2] = {0, 0};
    for (int i = 0; i < kc; i++)
        for (int j = 0; j < kc; j++) {
            int len = BC[i][j];
            BST[i][j] = DN;
            for (int c = 0; c < len; c++) {
                int t = DN++;
                dRow[t] = i;
                dCol[t] = j;
                dBS[t] = BST[i][j];
                dBL[t] = len;
                rowD[i][rc[i]++] = t;
                colD[j][cc[j]++] = t;
            }
        }
    VN = 2 * KC * GN;
}

static void set_dart(int t, int x) {
    dS[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        FWD[t][g] = gmul(g, x);
        BWD[t][g] = gmul(g, xi);
    }
}

/* Distinct labels inside each block keep the graph simple. */
static void random_init(void) {
    for (int t = 0; t < DN; t++) {
        int x;
        for (;;) {
            x = rndint(GN);
            int ok = 1;
            for (int u = dBS[t]; u < t; u++)
                if (dS[u] == x) { ok = 0; break; }
            if (ok) break;
        }
        set_dart(t, x);
    }
}

/* Left vertex (i,g) = i*GN + g; right vertex (j,h) = KC*GN + j*GN + h.
 * Left (i,g) ~ right (j, g*s); right (j,h) ~ left (i, h*s^-1). */
static int bfs_reach(int src) {
    stamp_++;
    int KN = KC * GN;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / GN, g = v - i * GN;
                for (int q = 0; q < d; q++) {
                    int t = rowD[i][q];
                    int u = KN + dCol[t] * GN + FWD[t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - KN, j = w / GN, h = w - j * GN;
                for (int q = 0; q < d; q++) {
                    int t = colD[j][q];
                    int u = dRow[t] * GN + BWD[t][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms, so one BFS per class representative
 * (identity element of each class) decides the diameter. */
static long cost_now(void) {
    long c = 0;
    for (int i = 0; i < KC; i++) {
        c += (long)VN - bfs_reach(i * GN);
        c += (long)VN - bfs_reach(KC * GN + i * GN);
    }
    return c;
}

static void save_best(const Comb *c) {
    bestC = *c;
    memcpy(bestS, dS, sizeof(int) * (size_t)DN);
}

static int search_comb(const Comb *c, double until) {
    setup_group(c->m, c->kk, c->r);
    setup_structure(c->K, c->a);
    if (GN < d) return 0;
    while (now() < until) {
        random_init();
        long cost = cost_now();
        if (cost == 0) { save_best(c); return 1; }
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if (now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int t = rndint(DN);
            int x = -1;
            for (int tr = 0; tr < 64; tr++) {
                int cand = rndint(GN), ok = 1;
                for (int u = dBS[t]; u < dBS[t] + dBL[t]; u++)
                    if (dS[u] == cand) { ok = 0; break; }
                if (ok) { x = cand; break; }
            }
            if (x < 0) continue;
            int old = dS[t];
            set_dart(t, x);
            long c2 = cost_now();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) { save_best(c); return 1; }
            } else {
                set_dart(t, old);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* All metacyclic groups of order N with m >= 2 (Z_N is m = N, k = 1, r = 1). */
static int push_groups(int N, int kc, int a, Comb *out, int n, int cap) {
    if (N < 2) return n;
    for (int m = 2; m <= N && n < cap; m++) {
        if (N % m) continue;
        int kk = N / m;
        for (int r = 1; r < m && n < cap; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, kk, m) != 1) continue;
            Comb c = {kc, m, kk, r, a};
            out[n++] = c;
        }
    }
    return n;
}

static int gen_combos(int V, Comb *out) {
    int n = 0;
    if (V % 2 == 0 && V / 2 <= MAXN)
        n = push_groups(V / 2, 1, 0, out, n, MAXCOMB);
    if (V % 4 == 0 && V / 4 <= MAXN) {
        for (int a = 1; a <= d - 1; a++)
            n = push_groups(V / 4, 2, a, out, n, MAXCOMB);
    }
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Comb tmp = out[i];
        out[i] = out[j];
        out[j] = tmp;
    }
    return n;
}

/* ------------------------------------------------------------ output */

static void print_result(void) {
    setup_group(bestC.m, bestC.kk, bestC.r);
    setup_structure(bestC.K, bestC.a);
    for (int t = 0; t < DN; t++) set_dart(t, bestS[t]);
    int N = GN, KN = KC * GN;
    long E = (long)DN * N;
    printf("%d %ld\n", 2 * KN, E);
    for (int t = 0; t < DN; t++)
        for (int g = 0; g < N; g++)
            printf("%d %d\n", dRow[t] * N + g, KN + dCol[t] * N + FWD[t][g]);
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
    t_end = t0 + limit * 0.95 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > 30 || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > 4L * MAXN) hi = 4L * MAXN;
    if (lo < 2 * d) lo = 2 * d;
    if (lo % 2) lo++;

    static Comb comb[MAXCOMB];
    int have = 0;
    /* Climb the vertex count V upward; each V gets a few random combinations. */
    for (long V = lo; V <= hi; V += 2) {
        if (t_end - now() < 0.3) break;
        int n = gen_combos((int)V, comb);
        int tries = n < MAXTRY ? n : MAXTRY;
        for (int ti = 0; ti < tries; ti++) {
            double rem = t_end - now();
            if (rem < 0.3) break;
            double slice = rem / 10.0;
            if (slice < 0.4) slice = 0.4;
            if (slice > 3.0) slice = 3.0;
            if (slice > rem) slice = rem;
            if (search_comb(&comb[ti], now() + slice)) {
                have = 1;
                break;
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
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

    # Search: bi-Cayley lifts (2 classes per side, metacyclic groups), climbing upward.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, min(mb // 4, 17000))
        hi = mb
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
