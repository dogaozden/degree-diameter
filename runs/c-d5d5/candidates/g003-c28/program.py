"""Combined bi-Cayley lift search (layered darts, metacyclic voltage groups, annealing in C).

Merged ideas
- Layered structure: k A-base vertices and k B-base vertices, with one permutation per
  layer. Every vertex then has degree exactly d, and the graph is bipartite by construction.
- Orbit-reduced diameter check: left translation is an automorphism that is transitive on
  each side, so a BFS to depth D from the 2k base representatives decides diameter <= D.
- Soft duplicate penalty (from the second parent) instead of a hard rejection, so annealing
  can pass through near-simple states.
- Ladder: the target order is always above the best valid order found, with an adaptive step.
- Python constructions (PG(2,q), Araujo-Pardo-Lopez, W(q)) are kept as valid starting points.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXD 32
#define MAXK2 64
#define MAXN 4096
#define ITERS 60000

typedef struct {
    int G, m, k2;
    long long r;
    long long pw[MAXK2];
} Group;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static long long lmod(long long a, long long m) { a %= m; if (a < 0) a += m; return a; }
static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b = lmod(b, m);
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Current lift state. */
static Group GRP;
static int K, DD, GG, NN, DIAM;
static int DJ[MAXK * MAXD], DS[MAXK * MAXD], DSI[MAXK * MAXD];
static int ADJ[MAXN * MAXD];
static int VIS[MAXN], QU[MAXN];
static int STAMP = 0;

/* Best state. */
static Group BG;
static int BK, BD, BGG;
static int BDJ[MAXK * MAXD], BDS[MAXK * MAXD];

/* Semidirect product Z_m x| Z_k2, element (a,b) coded as a*k2+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    const Group *g = &GRP;
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long long na = lmod((long long)a + g->pw[b] * (long long)c, g->m);
    int nb = (b + e) % g->k2;
    return (int)(na * g->k2 + nb);
}

static int ginv(int x) {
    const Group *g = &GRP;
    int a = x / g->k2, b = x % g->k2;
    int nb = (g->k2 - b) % g->k2;
    long long na = lmod(-g->pw[nb] * (long long)a, g->m);
    return (int)(na * g->k2 + nb);
}

static int random_group(int G) {
    int cand[MAXK2];
    int nc = 0;
    for (int k2 = 1; k2 <= MAXK2 && k2 <= G; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    int k2 = cand[rndint(nc)];
    int m = G / k2;
    long long r = 1 % m;
    if (k2 > 1) {
        for (int t = 0; t < 300; t++) {
            long long c = 1 + rndint(m - 1);
            if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
        }
    }
    GRP.G = G;
    GRP.m = m;
    GRP.k2 = k2;
    GRP.r = r;
    GRP.pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) GRP.pw[b] = (GRP.pw[b - 1] * r) % m;
    GG = G;
    return 1;
}

static void random_init(void) {
    for (int l = 0; l < DD; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            DJ[idx] = perm[i];
            DS[idx] = rndint(GG);
            DSI[idx] = ginv(DS[idx]);
        }
    }
}

/* Dart (l, i) joins A_{i,x} to B_{dj, x*s}. Each vertex gets exactly one slot per layer. */
static void build_adj(void) {
    for (int l = 0; l < DD; l++)
        for (int i = 0; i < K; i++) {
            int idx = l * K + i;
            int j = DJ[idx], s = DS[idx], si = DSI[idx];
            for (int x = 0; x < GG; x++) {
                int a = i * GG + x;
                ADJ[a * DD + l] = (K + j) * GG + gmul(x, s);
                int b = (K + j) * GG + x;
                ADJ[b * DD + l] = i * GG + gmul(x, si);
            }
        }
}

static int count_dups(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DD; l++)
            for (int l2 = l + 1; l2 < DD; l2++) {
                int a = l * K + i, b = l2 * K + i;
                if (DJ[a] == DJ[b] && DS[a] == DS[b]) c++;
            }
    return c;
}

/* Cost = unreached (representative, vertex) pairs + N per duplicated dart pair. */
static long long eval_cost(void) {
    int N = NN;
    long long cost = (long long)count_dups() * (long long)N;
    build_adj();
    for (int rep = 0; rep < 2 * K; rep++) {
        int src = rep * GG;
        if (++STAMP >= 0x7ffffff0) {
            memset(VIS, 0, sizeof(VIS));
            STAMP = 1;
        }
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = STAMP;
        for (int dep = 0; dep < DIAM && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int u = QU[head++];
                const int *au = ADJ + (size_t)u * DD;
                for (int t = 0; t < DD; t++) {
                    int v = au[t];
                    if (VIS[v] != STAMP) {
                        VIS[v] = STAMP;
                        QU[tail++] = v;
                    }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

static int anneal(long long iters, double T0, double T1, double tend) {
    long long cost = eval_cost();
    if (cost == 0) return 1;
    for (long long it = 0; it < iters; it++) {
        if ((it & 127) == 0 && cpu_now() > tend) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        long long c2;
        if (K >= 2 && rnd01() < 0.4) {
            /* swap the B-targets of two darts in one layer (keeps the layer a permutation) */
            int l = rndint(DD);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int a = l * K + i1, b = l * K + i2;
            int t = DJ[a]; DJ[a] = DJ[b]; DJ[b] = t;
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { t = DJ[a]; DJ[a] = DJ[b]; DJ[b] = t; }
        } else {
            /* change one voltage */
            int idx = rndint(DD * K);
            int os = DS[idx], osi = DSI[idx];
            int ns = rndint(GG);
            if (ns == os) continue;
            DS[idx] = ns;
            DSI[idx] = ginv(ns);
            c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[idx] = os; DSI[idx] = osi; }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void save_best(void) {
    BG = GRP;
    BK = K;
    BD = DD;
    BGG = GG;
    memcpy(BDJ, DJ, sizeof(DJ));
    memcpy(BDS, DS, sizeof(DS));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 20; w++) rnd64();
    int ch;
    while ((ch = getchar()) != EOF) {
    }
    if (d < 2 || DIAM < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    DD = d;

    double tend = cpu_now() + budget;
    int best_n = 0;
    int step = 8, fails = 0;

    while (cpu_now() < tend) {
        int k = 1 + rndint(MAXK);
        int target = best_n + step;
        int Gmin = (target + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        int G = Gmin + rndint(1 + Gmin / 16);
        int gcap = MAXN / (2 * k);
        if (G > gcap) G = gcap;
        if (G < 2) { fails++; continue; }
        K = k;
        if (!random_group(G)) { fails++; continue; }
        NN = 2 * K * GG;
        random_init();
        int ok = anneal(ITERS, 3.0, 0.15, tend);
        if (ok) {
            if (NN > best_n) {
                best_n = NN;
                save_best();
            }
            fails = 0;
            step *= 2;
            int cap = 16 + best_n / 8;
            if (step > cap) step = cap;
        } else if (++fails >= 3) {
            fails = 0;
            step /= 2;
            if (step < 2) step = 2;
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    GRP = BG;
    K = BK;
    DD = BD;
    GG = BGG;
    NN = 2 * K * GG;
    memcpy(DJ, BDJ, sizeof(DJ));
    memcpy(DS, BDS, sizeof(DS));
    for (int idx = 0; idx < K * DD; idx++) DSI[idx] = ginv(DS[idx]);
    build_adj();
    printf("%d %d\n", NN, K * GG * DD);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < GG; x++)
            for (int l = 0; l < DD; l++) {
                int a = i * GG + x;
                printf("%d %d\n", a, ADJ[a * DD + l]);
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (valid starting points and fallbacks).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _al(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for make in (lambda: _best_pg(d), lambda: _al(d)):
            try:
                g = make()
                if g is not None:
                    consider(g[0], g[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() - t0 < 0.1 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Main search in C, with a safety margin for compilation and output.
    deadline = t0 + time_limit - 3.0
    remaining = deadline - time.monotonic()
    if d >= 2 and D >= 2 and remaining > 4.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining - 2.0:.2f}"],
                             stdin_graph=None, timeout=remaining - 0.5)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
