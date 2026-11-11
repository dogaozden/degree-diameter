"""Voltage lifts over semidirect groups with a multi-vertex base for the bipartite degree-diameter problem.

New family in this version: a d-regular base multigraph on bs + bs vertices, given as d
permutations sigma_t of {0..bs-1}. Voltages s_t lie in a group G = Z_m x| Z_k of order N.
The lift has 2*bs*N vertices L_{i,g} and R_{j,h}, with edges L_{i,g} ~ R_{sigma_t(i), g*s_t}.
Each vertex has degree d, and the graph is bipartite by construction.

Left translations are automorphisms, so the diameter check needs only 2*bs BFS runs, one from
L_{i,e} and one from R_{j,e}. The C engine searches voltages and permutations by simulated
annealing. It climbs from a high starting order, gives each attempt a slice of the remaining
time, and keeps the last success, which is the largest order found. bs = 1 recovers the
Haar/semidirect family from before.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-vertex voltage lift search over Z_m x| Z_k.
 * Usage: prog d D seed time_limit nlo nhi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXN 6000
#define MAXV 48000
#define MAXE 800000

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

/* Group G = Z_GM x| Z_GK, element (a, b) coded as a*GK + b, product
 * (a,b)(c,e) = (a + r^b c, b + e). PW[b] = r^b mod GM. */
static int BS, GN, GK, GM, GR;
static int PW[MAXN];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + PW[b] * c) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}
static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (GM - (PW[nb] * a) % GM) % GM;
    return na * GK + nb;
}

/* Base: d permutations on BS points, one voltage per permutation. */
static int sig[MAXD][4], sinv[MAXD][4];
static int sv[MAXD], svi[MAXD];
static int fwd[MAXD][MAXN], bwd[MAXD][MAXN];
static int tmpF[MAXN], tmpB[MAXN];
static int vis[MAXV], que[MAXV];
static int stamp = 0;
static int EU[MAXE], EV[MAXE];
static int best_n = 0, best_m = 0;

static long gcdl(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}
static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void setup_group_random(int N) {
    GN = N;
    int divs[256], nd = 0;
    for (int k = 1; k <= N; k++)
        if (N % k == 0 && nd < 256) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int M = N / k, R = 0;
    if (M >= 2) {
        R = 1;
        for (int tr = 0; tr < 200; tr++) {
            int r = 1 + rndint(M - 1);
            if (gcdl(r, M) == 1 && powmodl(r, k, M) == 1) { R = r; break; }
        }
    }
    GK = k;
    GM = M;
    GR = R;
    PW[0] = 1 % M;
    for (int b = 1; b < GK; b++) PW[b] = (int)((long)PW[b - 1] * R % M);
}

static void set_volt(int t, int g) {
    sv[t] = g;
    svi[t] = ginv(g);
    for (int x = 0; x < GN; x++) {
        fwd[t][x] = gmul(x, g);
        bwd[t][x] = gmul(x, svi[t]);
    }
}

static void swap_perm(int t, int a, int b) {
    int ta = sig[t][a], tb = sig[t][b];
    sig[t][a] = tb;
    sig[t][b] = ta;
    sinv[t][tb] = a;
    sinv[t][ta] = b;
}

static void init_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < BS; i++) sig[t][i] = i;
        if (BS >= 2) {
            for (int i = BS - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = sig[t][i];
                sig[t][i] = sig[t][j];
                sig[t][j] = tmp;
            }
        }
        for (int i = 0; i < BS; i++) sinv[t][sig[t][i]] = i;
        set_volt(t, rndint(GN));
    }
}

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    int LN = BS * GN;
    stamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < LN) {
                int i = v / GN, g = v - i * GN;
                for (int t = 0; t < d; t++) {
                    int u = LN + sig[t][i] * GN + fwd[t][g];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            } else {
                int w = v - LN, j = w / GN, h = w - j * GN;
                for (int t = 0; t < d; t++) {
                    int u = sinv[t][j] * GN + bwd[t][h];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (source, vertex) pairs over the 2*BS fibre sources, plus a penalty for
 * parallel edges (two darts with the same voltage and the same target). */
static long eval_cost(void) {
    int LN = BS * GN, V = 2 * LN;
    long unr = 0;
    for (int i = 0; i < BS; i++) unr += V - bfs_reach(i * GN);
    for (int j = 0; j < BS; j++) unr += V - bfs_reach(LN + j * GN);
    long dup = 0;
    for (int t = 0; t < d; t++)
        for (int u = t + 1; u < d; u++)
            if (sv[t] == sv[u])
                for (int i = 0; i < BS; i++)
                    if (sig[t][i] == sig[u][i]) dup++;
    return unr + 20 * dup;
}

static int sa_run(double until) {
    const int iters = 6000;
    while (now() < until) {
        init_state();
        long cost = eval_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters; it++) {
            if (now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d);
            int kind = (BS >= 2 && rnd01() < 0.2) ? 1 : 0;
            int oldg = sv[t], a = 0, b = 0;
            if (kind == 0) {
                int g = rndint(GN);
                if (g == oldg) continue;
                memcpy(tmpF, fwd[t], sizeof(int) * GN);
                memcpy(tmpB, bwd[t], sizeof(int) * GN);
                set_volt(t, g);
            } else {
                a = rndint(BS);
                do { b = rndint(BS); } while (b == a);
                swap_perm(t, a, b);
            }
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else if (kind == 0) {
                memcpy(fwd[t], tmpF, sizeof(int) * GN);
                memcpy(bwd[t], tmpB, sizeof(int) * GN);
                sv[t] = oldg;
                svi[t] = ginv(oldg);
            } else {
                swap_perm(t, a, b);
            }
        }
    }
    return 0;
}

static void emit_best(void) {
    int LN = BS * GN, cnt = 0;
    for (int i = 0; i < BS; i++)
        for (int g = 0; g < GN; g++)
            for (int t = 0; t < d; t++) {
                EU[cnt] = i * GN + g;
                EV[cnt] = LN + sig[t][i] * GN + fwd[t][g];
                cnt++;
            }
    best_n = 2 * LN;
    best_m = cnt;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long nlo = atol(argv[5]), nhi = atol(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (nlo < 2 * d) nlo = 2 * d;
    if (nlo % 2) nlo++;

    /* Base sizes are tried in this order for each target order n = 2*bs*N. */
    static const int order[4] = {2, 3, 4, 1};
    for (long n = nlo; n <= nhi; n += 2) {
        if (now() > t_end - 0.3) break;
        for (int oi = 0; oi < 4; oi++) {
            int bs = order[oi];
            if (n % (2L * bs)) continue;
            long N = n / (2L * bs);
            if (N < d || N > MAXN) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            double slice = 0.06 * rem;
            if (slice < 0.5) slice = 0.5;
            if (slice > rem) slice = rem;
            BS = bs;
            setup_group_random((int)N);
            if (sa_run(now() + slice)) {
                emit_best();
                break;
            }
        }
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", EU[e], EV[e]);
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

    # Search: multi-vertex voltage lifts over Z_m x| Z_k, starting high in the order range.
    if d >= 3 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
        nlo = max(best[0] + 2, mb // 4)
        nhi = mb
        if budget > 3.0 and nlo <= nhi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo, nhi],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
