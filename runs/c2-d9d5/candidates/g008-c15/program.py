"""Semidirect-product affine lifts for the bipartite degree-diameter problem.

Change in this version: the group family is replaced. The parent used
F_q x| H (field-based), which is cyclic-like for the best orders. Here the group is
G = Z_m x|_r Z_k with r^k = 1 (mod m), gcd(r, m) = 1, chosen at random for each
order N = m*k. This includes abelian (r = 1) and cyclic (k = 1) groups, and
non-abelian ones. The base uses B in {1, 2, 3, 4} orbits per side. Each dart slot
is a random permutation of the orbits, so every base is d-regular.

Left translations and right translations by G are automorphisms of the lift, and
each side's orbit is transitive. BFS from the 2B orbit representatives therefore
decides the diameter. Simulated annealing over voltages minimises the number of
(representative, vertex) pairs not reached within D steps. Orders are searched by
bisection per B, and each success raises the best total.

Python keeps the earlier small constructions (projective plane incidence,
Araujo-Pardo-Lopez, W(q) for D = 4) as fallbacks, checks every candidate with
lib.is_valid, and returns the largest valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Semidirect-product affine lifts: G = Z_m x|_r Z_k, order N = m*k.
 * B orbits per side (B <= d), d-regular base = union of d random permutations.
 * Dart (i,t) with voltage v: L(i,g) ~ R(tgt[i][t], g*v).
 * Usage: prog d D seed time_limit initial_total
 * Output: "V E" then E lines "u v" (u on the left, v on the right), or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXB 4
#define MAXN 10000
#define MAXV 20000
#define ITERS 20000

static int dd, DD;
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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long res = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) res = res * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)res;
}

static double moore_bound(int d, int D) {
    if (D == 0 || d == 0) return 1.0;
    if (d == 2) return 2.0 * D;
    double s = 0.0, p = 1.0;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2.0 * s;
}

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

static int GM, GK, GR, GN;
static int pwr[MAXN];      /* pwr[b] = r^b mod m */
static int rlist[MAXN];

static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        pwr[b] = (int)p;
        p = (p * r) % m;
    }
}

/* Element (a, b) is coded a*K + b. (a,b)(c,e) = (a + r^b c, b + e). */
static inline int gmul(int x, int y) {
    int a = x / GK, b = x - a * GK;
    int c = y / GK, e = y - c * GK;
    long na = (a + (long)pwr[b] * c) % GM;
    int nb = b + e;
    if (nb >= GK) nb -= GK;
    return (int)na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x - a * GK;
    int nb = (GK - b) % GK;
    long na = (GM - ((long)pwr[nb] * a) % GM) % GM;
    return (int)na * GK + nb;
}

/* Choose a random admissible (m, k, r) with m*k = N, m >= 2. */
static int pick_group(int N, int *pm, int *pk, int *pr) {
    int divs[128], nd = 0;
    for (int dv = 2; dv <= N && nd < 128; dv++)
        if (N % dv == 0) divs[nd++] = dv;
    if (nd == 0) return 0;
    for (int tries = 0; tries < 16; tries++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int cnt = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1) rlist[cnt++] = r;
        if (cnt == 0) continue;
        *pm = m;
        *pk = k;
        *pr = rlist[rndint(cnt)];
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ lift state */

static int BB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stampc = 0;
static int adjv[MAXV][MAXD];

static int have = 0, bestTotal = 0, bestB, bestM, bestK, bestR;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static int base_connected(int B) {
    int sL[MAXB], sR[MAXB];
    for (int i = 0; i < B; i++) { sL[i] = 0; sR[i] = 0; }
    sL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < dd; t++) {
                int j = tgt[i][t];
                if (sL[i] && !sR[j]) { sR[j] = 1; changed = 1; }
                if (sR[j] && !sL[i]) { sL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!sL[i] || !sR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= dd) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != dd) return 0;
    return 1;
}

static void random_pattern(int B) {
    for (;;) {
        for (int t = 0; t < dd; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected(B) && set_incidence(B)) break;
    }
    BB = B;
}

/* Darts from the same left orbit to the same right orbit need distinct voltages. */
static int valid_val(int i, int t, int x) {
    for (int t2 = 0; t2 < dd; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    int xi = ginv(x);
    vol[i][t] = x;
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

static int init_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) vol[i][t] = -1;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) {
            int ok = 0;
            for (int tr = 0; tr < 20000 && !ok; tr++) {
                int x = rndint(GN);
                if (valid_val(i, t, x)) { ok = 1; vol[i][t] = x; }
            }
            if (!ok) return 0;
        }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) set_dart(i, t, vol[i][t]);
    return 1;
}

/* Number of vertices within distance DD of src. */
static int bfs_reach(int src) {
    int N = GN, BN = BB * N;
    int head = 0, tail = 0;
    stampc++;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v - i * N;
                for (int t = 0; t < dd; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w - j * N;
                for (int k = 0; k < dd; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached (representative, vertex) pairs. Zero means diameter <= DD. */
static long cover_cost(void) {
    int N = GN, V = 2 * BB * N;
    long cost = 0;
    for (int i = 0; i < BB; i++) cost += V - bfs_reach(i * N);
    for (int j = 0; j < BB; j++) cost += V - bfs_reach((BB + j) * N);
    return cost;
}

/* Simulated annealing over voltages with the base fixed. */
static int anneal(double until) {
    long cost = cover_cost();
    if (cost == 0) return 1;
    double Ts = 0.1 * (double)cost + 1.0, Te = 0.2;
    for (int it = 0; it < ITERS; it++) {
        if ((it & 31) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / ITERS);
        int i = rndint(BB), t = rndint(dd);
        int x = -1;
        for (int tr = 0; tr < 64; tr++) {
            int y = rndint(GN);
            if (y != vol[i][t] && valid_val(i, t, y)) { x = y; break; }
        }
        if (x < 0) continue;
        int old = vol[i][t];
        set_dart(i, t, x);
        long c2 = cover_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            set_dart(i, t, old);
        }
    }
    return 0;
}

static void record(int B) {
    have = 1;
    bestTotal = 2 * B * GN;
    bestB = B;
    bestM = GM;
    bestK = GK;
    bestR = GR;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Full BFS on the explicit adjacency (adjv), used as a final safety check. */
static int bfs_full(int src) {
    int head = 0, tail = 0;
    stampc++;
    que[tail++] = src;
    vis[src] = stampc;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int k = 0; k < dd; k++) {
                int u = adjv[v][k];
                if (vis[u] != stampc) { vis[u] = stampc; que[tail++] = u; }
            }
        }
    }
    return tail;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int init_total = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (dd < 2 || dd > MAXD || DD < 2) { printf("0 0\n"); return 0; }

    double mb = moore_bound(dd, DD);
    bestTotal = init_total;
    have = 0;

    int Bmax = dd < MAXB ? dd : MAXB;
    long lo[MAXB + 1], hi[MAXB + 1];
    int fl[MAXB + 1];
    for (int B = 1; B <= Bmax; B++) {
        double capd = mb / (2.0 * B);
        long cap = capd < (double)(MAXN - 1) ? (long)capd : (long)(MAXN - 1);
        long capv = MAXV / (2 * B);
        if (cap > capv) cap = capv;
        long l0 = bestTotal / (2 * B);
        if (l0 < dd) l0 = dd;
        lo[B] = l0;
        hi[B] = cap + 1;
        fl[B] = 0;
    }

    int rounds = 0;
    while (now() < t_end) {
        int active = 0;
        for (int B = 1; B <= Bmax; B++) {
            long l1 = bestTotal / (2 * B);
            if (lo[B] < l1) lo[B] = l1;
            if (hi[B] - lo[B] > 1) active = 1;
        }
        if (!active) break;

        int B = 1 + (rounds++ % Bmax);
        if (hi[B] - lo[B] <= 1) continue;

        long N = lo[B] + (hi[B] - lo[B]) / 2;
        if (N <= lo[B]) N = lo[B] + 1;
        int m, k, r;
        if (!pick_group((int)N, &m, &k, &r)) { hi[B] = N; continue; }
        setup_group(m, k, r);
        BB = B;

        double att = now() + 3.0;
        if (att > t_end) att = t_end;
        int ok = 0;
        while (!ok && now() < att) {
            random_pattern(B);
            if (!init_state(B)) continue;
            if (anneal(att)) ok = 1;
        }
        if (ok) {
            if (2 * B * GN > bestTotal) record(B);
            lo[B] = N;
            fl[B] = 0;
        } else if (++fl[B] >= 2) {
            hi[B] = N;
            fl[B] = 0;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }

    /* Rebuild the best graph from its stored parameters. */
    int B = bestB;
    setup_group(bestM, bestK, bestR);
    BB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) { printf("0 0\n"); return 0; }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < dd; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN;
    if (V > MAXV) { printf("0 0\n"); return 0; }
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v - i * N;
        for (int t = 0; t < dd; t++)
            adjv[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) - j * N;
        for (int k2 = 0; k2 < dd; k2++) {
            int i = incI[j][k2], t = incT[j][k2];
            adjv[w][k2] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour. */
    for (int v = 0; v < V; v++)
        for (int k2 = 0; k2 < dd; k2++)
            for (int l = 0; l < k2; l++)
                if (adjv[v][k2] == adjv[v][l]) { printf("0 0\n"); return 0; }

    /* Full diameter check when cheap. */
    if (V <= 6000) {
        for (int s = 0; s < V; s++)
            if (bfs_full(s) != V) { printf("0 0\n"); return 0; }
    }

    printf("%d %d\n", V, BN * dd);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < dd; t++)
            printf("%d %d\n", v, adjv[v][t]);
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
        # Exact Moore graph for D = 3: nothing can beat it.
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

    # Semidirect-product affine lifts searched by C; leave room for compile and checks.
    if 2 <= d <= 32 and D >= 3:
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 4.0
        if budget > 4.0:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2), best[0]],
                                 stdin_graph=None, timeout=budget + 10.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
