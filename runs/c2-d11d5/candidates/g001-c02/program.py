"""Combined program: known constructions in Python, then a C bi-Cayley lift search.

Python: Moore/projective-plane, Araujo-Pardo-Lopez and generalized-quadrangle baselines.
C: simulated annealing over voltage lifts of bi-Cayley graphs on semidirect products
Z_m x| Z_k2 (incremental edge rebuilds, bitset reachability, stagnation restarts), starting
from the best graph so far, with the best valid result kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 12288
#define MAXD 32
#define MAXK 4
#define MAXK2 64
#define MAXE 300000
#define PEN 1000L

static int d, D;
static long moore;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long powmod(long b, long e, long m) {
    long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p; p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ generic check */

static int ad[MAXV][MAXD];
static int dg[MAXV];
static int colr[MAXV], qu[MAXV];

static int build_adj(int n, int E, const int *eu, const int *ev) {
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (dg[u] >= MAXD || dg[v] >= MAXD) return 0;
        ad[u][dg[u]++] = v;
        ad[v][dg[v]++] = u;
    }
    for (int v = 0; v < n; v++) {
        if (dg[v] > d) return 0;
        for (int i = 0; i < dg[v]; i++)
            for (int j = 0; j < i; j++)
                if (ad[v][i] == ad[v][j]) return 0;
    }
    return 1;
}

static int is_bip(int n) {
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] != -1) continue;
        colr[s] = 0;
        int h = 0, t = 0;
        qu[t++] = s;
        while (h < t) {
            int v = qu[h++];
            for (int i = 0; i < dg[v]; i++) {
                int u = ad[v][i];
                if (colr[u] == -1) { colr[u] = 1 - colr[v]; qu[t++] = u; }
                else if (colr[u] == colr[v]) return 0;
            }
        }
    }
    return 1;
}

/* Number of unordered pairs at distance > D (using current ad/dg). */
static long bad_pairs_adj(int n) {
    int W = (n + 63) / 64;
    size_t sz = (size_t)n * W;
    uint64_t *cur = malloc(sizeof(uint64_t) * sz);
    uint64_t *nxt = malloc(sizeof(uint64_t) * sz);
    if (!cur || !nxt) { free(cur); free(nxt); return -1; }
    memset(cur, 0, sizeof(uint64_t) * sz);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
            for (int i = 0; i < dg[v]; i++) {
                const uint64_t *s = cur + (size_t)ad[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    free(cur); free(nxt);
    return total / 2;
}

static int full_valid(int n, int E, const int *eu, const int *ev) {
    if (n < 1 || n > MAXV || E < 0 || E > MAXE) return 0;
    if (n > moore) return 0;
    if (!build_adj(n, E, eu, ev)) return 0;
    if (!is_bip(n)) return 0;
    return bad_pairs_adj(n) == 0;
}

/* ------------------------------------------------------------ best graph store */

static int bn = 0, bE = 0;
static int bu[MAXE], bv[MAXE];
static int TU[MAXE], TV[MAXE];

static void store_best(int n, int E, const int *eu, const int *ev) {
    bn = n; bE = E;
    memcpy(bu, eu, sizeof(int) * E);
    memcpy(bv, ev, sizeof(int) * E);
}

static void store_complete(void) {
    int E = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) { TU[E] = a; TV[E] = d + b; E++; }
    store_best(2 * d, E, TU, TV);
}

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++)
        if (scanf("%d %d", &TU[e], &TV[e]) != 2) return;
    if (n > bn && full_valid(n, m, TU, TV)) store_best(n, m, TU, TV);
}

static void print_best(void) {
    printf("%d %d\n", bn, bE);
    for (int e = 0; e < bE; e++) printf("%d %d\n", bu[e], bv[e]);
}

/* ------------------------------------------------------------ bi-Cayley lifts */

/* Group Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). Order G = M*K2. */
static int K, G, M, K2;
static int RP[MAXK2];
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK], SI[MAXD][MAXK];
static int NB[MAXD][MAXV];
static uint32_t RA[MAXV], RB[MAXV];
static uint32_t *last_reach = RA;

static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    long t = (a + (long)RP[b] * c) % M;
    int f = b + e;
    if (f >= K2) f -= K2;
    return (int)t * K2 + f;
}

static int rinv(int y) {
    int a = y / K2, b = y - a * K2;
    int nb = (K2 - b) % K2;
    long c = (M - (long)a * RP[nb] % M) % M;
    return (int)c * K2 + nb;
}

/* Recompute the neighbour table entries touched by dart (layer l, A-block i). */
static void set_dart(int l, int i) {
    int p = lay[l][i], s = S[l][i], si = rinv(s);
    SI[l][i] = si;
    int Bbase = (K + p) * G;
    for (int x = 0; x < G; x++) NB[l][i * G + x] = Bbase + gmul(x, s);
    for (int h = 0; h < G; h++) NB[l][Bbase + h] = i * G + gmul(h, si);
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) { lay[l][i] = perm[i]; S[l][i] = rndint(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (lay[l1][i] == lay[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

/* Number of unreached (representative block, vertex) pairs. Zero means diameter <= D. */
static long reach_cost(void) {
    int N = 2 * K * G;
    uint32_t *cur = RA, *nxt = RB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int ch = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[NB[l][v]];
            nxt[v] = x;
            if (x != cur[v]) ch = 1;
        }
        uint32_t *t = cur; cur = nxt; nxt = t;
        if (!ch) break;
    }
    long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - __builtin_popcount(cur[v]);
    last_reach = cur;
    return unr;
}

static int sa_run(int iters, int patience) {
    int N = 2 * K * G;
    uint32_t full = (1u << (2 * K)) - 1u;
    long cost = reach_cost() + PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now() > t_end) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* layer swap: exchange the B-targets of two A-blocks in one layer */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            long c2 = reach_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        /* voltage move: defect-targeted with probability 0.4 */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int u = -1;
            for (int tr = 0; tr < 64; tr++) {
                int v = rndint(N);
                if (last_reach[v] != full) { u = v; break; }
            }
            if (u >= 0) {
                int block = u / G;
                int ll = rndint(d);
                if (block < K) { l = ll; i = block; }
                else {
                    for (int ii = 0; ii < K; ii++)
                        if (lay[ll][ii] == block - K) { l = ll; i = ii; break; }
                }
            }
        }
        if (l < 0) { l = rndint(d); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = reach_cost() + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static int extract_lift(int *eu, int *ev) {
    int E = 0;
    for (int v = 0; v < K * G; v++)
        for (int l = 0; l < d; l++) { eu[E] = v; ev[E] = NB[l][v]; E++; }
    return E;
}

static const int KCH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Random Z_M x| Z_K2 with order at least target. */
static int choose_group(int target) {
    int nch = (int)(sizeof(KCH) / sizeof(KCH[0]));
    for (int att = 0; att < 200; att++) {
        int k2 = KCH[rndint(nch)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r = -1;
        if (k2 == 1) r = 1 % m;
        else if (m < 3) r = 1;
        else if (k2 == 2 && rndint(10) < 3) r = m - 1;
        else {
            for (int t = 0; t < 60; t++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        M = m; K2 = k2; G = m * k2;
        RP[0] = 1 % m;
        for (int b = 1; b < K2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static void search(void) {
    int wins[MAXK + 1], trials[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { wins[k] = 0; trials[k] = 0; }
    static int EU[MAXE], EV[MAXE];
    while (now() < t_end) {
        int k;
        if (rnd01() < 0.2) k = 1 + rndint(MAXK);
        else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int base = bn / (2 * k) + 1;
        int target = base + rndint(base / 8 + 2);
        if (!choose_group(target)) continue;
        long N = 2L * k * G;
        if (N <= bn || N > moore || N > MAXV) continue;
        K = k;
        trials[k]++;
        random_lift();
        if (sa_run(4000, 1200)) {
            int E = extract_lift(EU, EV);
            if (N > bn && full_valid((int)N, E, EU, EV)) {
                store_best((int)N, E, EU, EV);
                wins[k]++;
            }
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || d > MAXD || D < 1) { printf("1 0\n"); return 0; }
    moore = moore_bound();
    if (D == 1) {
        TU[0] = 0; TV[0] = 1;
        store_best(2, 1, TU, TV);
    } else {
        store_complete();
    }
    read_start();
    if (D >= 2 && d >= 2 && bn < moore) search();
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (baselines and start graphs).
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2 and optimal for D == 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        if lib.is_prime_power(d - 1):
            return best  # Moore graph: optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ag = lib.araujo_lopez_graph(d - 2)
                consider(ag[0], ag[1])
            except Exception:
                pass
    if D == 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if best[0] >= lib.moore_bound(d, D):
        return best
    if d > 32:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except Exception:
        pass
    return best
