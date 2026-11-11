"""Two-class voltage lifts over affine groups for the bipartite degree-diameter problem.

Idea: the parent searches Haar graphs, which are one-class lifts: a single base vertex
per side with d darts, so the order is 2|G|. This version uses a two-class base:
left classes a in {0,1} and right classes b in {0,1}, with M[a][b] darts from a to b,
where M = [[x, d-x], [d-x, x]] (row and column sums d). The lift has order 4|G| over
G = F_q x| H, with edges L(a,g) ~ R(b, g*s) for each dart (a,b,s). Left translation
by G is an automorphism, so the diameter check needs only 4 BFS runs, one from each
class representative. Graphs of this kind have a different order-to-group-size ratio
from the Haar family, so they can reach orders the parent's search misses.

The search anneals the dart elements, with iterated perturbation of the incumbent,
and picks the matrix split x at random on each fresh restart. Candidates are tried in
ascending order of total order, with a time slice per candidate. The Python side keeps
a valid fallback at every step.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-class voltage lift search over affine groups F_q x| H.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
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
#define MAXN 8192
#define MAXT 2
#define MAXD 32
#define MAXK (MAXT * MAXD)
#define MAXV (2 * MAXT * MAXN)
#define MAXCAND 20000

typedef struct { int q, p, k, c, tc, N, V; } Cand;

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

static int TC, GN, GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded a*c + j, with h_j = g^(j*(q-1)/c). Product:
 * (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
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

/* ------------------------------------------------------------ two-class lift state */

/* Left vertex (a, g) = a*GN + g; right vertex (b, h) = NT + b*GN + h, NT = TC*GN.
 * Dart k joins class dA[k] on the left to class dB[k] on the right with element dS[k]:
 * L(a,g) ~ R(b, g*s), so R(b,h) ~ L(a, h*s^-1). */
static int nd, curx;
static int MX[MAXT][MAXT];
static int dA[MAXK], dB[MAXK], dS[MAXK], dSi[MAXK];
static int fwd[MAXK][MAXN], bwd[MAXK][MAXN];
static int LD[MAXT][MAXD], RD[MAXT][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int incds[MAXK], bestDs[MAXK];

static void setup_matrix(int x) {
    for (int a = 0; a < TC; a++)
        for (int b = 0; b < TC; b++) MX[a][b] = 0;
    if (TC == 1) {
        MX[0][0] = d;
    } else {
        MX[0][0] = x;
        MX[0][1] = d - x;
        MX[1][0] = d - x;
        MX[1][1] = x;
    }
    nd = 0;
    for (int a = 0; a < TC; a++)
        for (int b = 0; b < TC; b++)
            for (int r = 0; r < MX[a][b]; r++) {
                dA[nd] = a;
                dB[nd] = b;
                nd++;
            }
    int cl[MAXT] = {0}, cr[MAXT] = {0};
    for (int k = 0; k < nd; k++) {
        LD[dA[k]][cl[dA[k]]++] = k;
        RD[dB[k]][cr[dB[k]]++] = k;
    }
}

static void set_dart(int k, int x) {
    dS[k] = x;
    dSi[k] = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[k][g] = gmul(g, x);
        bwd[k][g] = gmul(g, dSi[k]);
    }
}

/* True if element x is already used by another dart on the same class pair. */
static int conflicts(int k, int x) {
    for (int j = 0; j < nd; j++)
        if (j != k && dA[j] == dA[k] && dB[j] == dB[k] && dS[j] == x) return 1;
    return 0;
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int NT = TC * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < NT) {
                int a = v / GN, g = v % GN;
                for (int i = 0; i < d; i++) {
                    int k = LD[a][i];
                    int u = NT + dB[k] * GN + fwd[k][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - NT, b = w / GN, h = w % GN;
                for (int i = 0; i < d; i++) {
                    int k = RD[b][i];
                    int u = dA[k] * GN + bwd[k][h];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Vertex-transitivity within each class: one BFS per class representative
 * (L(a,e) and R(b,e)) decides the diameter. */
static long cover_cost(void) {
    int NT = TC * GN, V = 2 * NT;
    long c = 0;
    for (int a = 0; a < TC; a++) {
        c += (long)(V - bfs_count(a * GN));
        c += (long)(V - bfs_count(NT + a * GN));
    }
    return c;
}

/* Simulated annealing over dart elements, starting from a state with the given cost.
 * The state always matches the returned cost, so an early stop is safe. */
static long anneal(long cost, double Ts, int iters, double until) {
    const double Te = 0.3;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) break;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        int k = rndint(nd), y;
        do { y = rndint(GN); } while (conflicts(k, y));
        int old = dS[k];
        set_dart(k, y);
        long c2 = cover_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            set_dart(k, old);
        }
    }
    return cost;
}

/* Fresh random restarts, each followed by iterated annealing around the incumbent.
 * Returns 1 when the current state has cost 0 (diameter <= D), 0 on timeout. */
static int search_cfg(double until) {
    const int iters = 6000, rounds = 6;
    while (now() < until) {
        curx = (TC == 1) ? d : 1 + rndint(d / 2);
        setup_matrix(curx);
        for (int k = 0; k < nd; k++) {
            int y;
            do { y = rndint(GN); } while (conflicts(k, y));
            set_dart(k, y);
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        cost = anneal(cost, 0.05 * (double)cost + 1.0, iters, until);
        if (cost == 0) return 1;
        long bestc = cost;
        memcpy(incds, dS, sizeof(int) * (size_t)nd);
        for (int r = 0; r < rounds && now() < until; r++) {
            for (int k = 0; k < nd; k++) set_dart(k, incds[k]);
            for (int t2 = 0; t2 < 2; t2++) {
                int k = rndint(nd), y;
                do { y = rndint(GN); } while (conflicts(k, y));
                set_dart(k, y);
            }
            cost = cover_cost();
            if (cost == 0) return 1;
            cost = anneal(cost, 0.02 * (double)cost + 1.0, iters, until);
            if (cost == 0) return 1;
            if (cost < bestc) {
                bestc = cost;
                memcpy(incds, dS, sizeof(int) * (size_t)nd);
            }
        }
    }
    return 0;
}

static void print_result(void) {
    int NT = TC * GN;
    printf("%d %d\n", 2 * NT, NT * d);
    for (int a = 0; a < TC; a++)
        for (int g = 0; g < GN; g++)
            for (int i = 0; i < d; i++) {
                int k = LD[a][i];
                printf("%d %d\n", a * GN + g, NT + dB[k] * GN + fwd[k][g]);
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
    long lo = atol(argv[5]), hi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXV) hi = MAXV;

    static Cand cand[MAXCAND];
    int nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1 && c < MAXC; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N > MAXN || N <= d) continue;
            for (int tc = 1; tc <= MAXT; tc++) {
                long V = 2L * tc * N;
                if (V < lo || V > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {q, p, k, c, tc, (int)N, (int)V};
                    cand[nc++] = cd;
                }
            }
        }
    }
    /* Insertion sort by total order, ascending. */
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].V > t.V) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int bestV = 0, bq = 0, bp = 0, bk = 0, bc = 0, btc = 0, bx = 0;
    for (int ci = 0; ci < nc; ci++) {
        Cand cd = cand[ci];
        if (cd.V <= bestV) continue;
        double rem = t_end - now();
        if (rem < 0.3) break;
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cd.q, cd.p, cd.k, cd.c);
        TC = cd.tc;
        if (search_cfg(now() + slice)) {
            bestV = cd.V;
            bq = cd.q; bp = cd.p; bk = cd.k; bc = cd.c; btc = cd.tc;
            bx = curx;
            memcpy(bestDs, dS, sizeof(int) * (size_t)nd);
        }
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bq, bp, bk, bc);
    TC = btc;
    setup_matrix(bx);
    for (int k = 0; k < nd; k++) set_dart(k, bestDs[k]);
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

    # Search: two-class voltage lifts over affine groups, with total order in a wide range.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 6)
        hi = mb // 2
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
