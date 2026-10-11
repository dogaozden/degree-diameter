import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley (group voltage) lifts.
#
# Base: k "A" vertices and k "B" vertices. Each layer l is a permutation p_l of
# the B indices, so every A_i and every B_j has exactly d darts. Dart (l, i) has
# voltage s in the group H and joins A_{i,g} to B_{p_l(i), g*s} for all g in H.
#
# H is a random semidirect product Z_m x| Z_k2 (element a*k2+b), built inside C.
# Left multiplication by any h is an automorphism of the lift, so the diameter
# is <= D iff a BFS of depth D from each of the 2k representatives A_{i,e},
# B_{j,e} reaches every vertex. The cost is the total number of unreached
# (representative, vertex) pairs, plus a penalty per duplicate edge.
# Moves: change one voltage, or swap two B-targets inside one layer.
# The engine climbs the target order: it accepts any lift larger than the
# incumbent, and echoes the incumbent when it finds nothing larger.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXL 40
#define MAXK 4
#define MAXG 1200
#define MAXV (2*MAXK*MAXG)

static uint64_t rs = 1;
static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d, D, k, G, N;
static int *mulT = NULL;   /* G*G table: mulT[x*G+y] = x*y */
static int *invT = NULL;
static int pm[MAXL][MAXK]; /* B index of A_i in layer l (a permutation per layer) */
static int sm[MAXL][MAXK]; /* voltage of dart (l, i) */
static int adjL[MAXV * MAXL];
static int degA[MAXV];
static int stampA[MAXV];
static int queueA[MAXV];
static int curStamp = 0;
static clock_t t_start;
static double budget_s;

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m; if (b < 0) b += m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int time_up(void) {
    return (double)(clock() - t_start) / CLOCKS_PER_SEC >= budget_s;
}

/* Random semidirect product Z_m x| Z_k2 of the given order (element a*k2+b). */
static int build_group(int order) {
    int divs[64], nd = 0;
    for (int k2 = 1; k2 <= 12 && k2 <= order; k2++)
        if (order % k2 == 0 && order / k2 >= 2) divs[nd++] = k2;
    if (nd == 0) return 0;
    for (int attempt = 0; attempt < 60; attempt++) {
        int k2 = divs[rndint(nd)];
        int m = order / k2;
        int r = 1 % m;
        if (k2 > 1) {
            int ok = 0;
            for (int t = 0; t < 300; t++) {
                int cand = 1 + rndint(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) { r = cand; ok = 1; break; }
            }
            if (!ok) continue;
        }
        int *pw = malloc(sizeof(int) * k2);
        pw[0] = 1 % m;
        for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
        int *mt = malloc(sizeof(int) * (size_t)order * order);
        for (int x = 0; x < order; x++) {
            int a = x / k2, b = x % k2;
            for (int y = 0; y < order; y++) {
                int c = y / k2, e = y % k2;
                int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
                int bb = (b + e) % k2;
                mt[x * order + y] = aa * k2 + bb;
            }
        }
        free(pw);
        int *it = malloc(sizeof(int) * order);
        for (int s = 0; s < order; s++) {
            it[s] = 0;
            for (int y = 0; y < order; y++) if (mt[s * order + y] == 0) { it[s] = y; break; }
        }
        free(mulT); free(invT);
        mulT = mt; invT = it; G = order;
        return 1;
    }
    return 0;
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) degA[v] = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = pm[l][i], s = sm[l][i];
            int ub = i * G, vb = (k + j) * G;
            for (int g = 0; g < G; g++) {
                int a = ub + g;
                int b = vb + mulT[g * G + s];
                adjL[a * d + degA[a]++] = b;
                adjL[b * d + degA[b]++] = a;
            }
        }
}

static int unreached_from(int src) {
    if (++curStamp >= 0x7ffffff0) { memset(stampA, 0, sizeof(stampA)); curStamp = 1; }
    int tail = 0;
    queueA[tail++] = src;
    stampA[src] = curStamp;
    int fs = 0, fe = 1;
    for (int lev = 0; lev < D && fs < fe; lev++) {
        for (int q = fs; q < fe; q++) {
            int u = queueA[q];
            const int *au = adjL + u * d;
            for (int t = 0; t < d; t++) {
                int v = au[t];
                if (stampA[v] != curStamp) { stampA[v] = curStamp; queueA[tail++] = v; }
            }
        }
        fs = fe;
        fe = tail;
    }
    return N - tail;
}

static long long eval_cost(void) {
    long long c = 0;
    /* duplicate darts (same A_i, same B_j, same voltage) give duplicate edges */
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pm[l1][i] == pm[l2][i] && sm[l1][i] == sm[l2][i]) c += N;
    build_adj();
    for (int cidx = 0; cidx < 2 * k; cidx++) c += unreached_from(cidx * G);
    return c;
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { pm[l][i] = perm[i]; sm[l][i] = rndint(G); }
    }
}

/* Returns 1 if a lift with diameter <= D was found (state is then valid). */
static int anneal(long long iters) {
    random_state();
    long long cost = eval_cost();
    const double T0 = 1.5, T1 = 0.05;
    for (long long it = 0; it < iters; it++) {
        if (cost == 0) return 1;
        if ((it & 255) == 0 && time_up()) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int l = rndint(d);
        if (k == 1 || rnd01() < 0.5) {
            int i = rndint(k);
            int old = sm[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            sm[l][i] = nv;
            long long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else sm[l][i] = old;
        } else {
            int i1 = rndint(k), i2 = rndint(k);
            if (i1 == i2) continue;
            int t = pm[l][i1]; pm[l][i1] = pm[l][i2]; pm[l][i2] = t;
            long long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else { t = pm[l][i1]; pm[l][i1] = pm[l][i2]; pm[l][i2] = t; }
        }
    }
    return cost == 0;
}

static int *bestE = NULL;
static int bestM = 0;
static int bestN = 0;

static void emit_lift(int *out) {
    int c = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            for (int g = 0; g < G; g++) {
                out[2 * c] = i * G + g;
                out[2 * c + 1] = (k + pm[l][i]) * G + mulT[g * G + sm[l][i]];
                c++;
            }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    budget_s = atof(argv[4]);
    t_start = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (m0 < 0) m0 = 0;
    int *inE = malloc(sizeof(int) * (2 * (size_t)m0 + 2));
    int got = 0;
    for (; got < m0; got++)
        if (scanf("%d %d", &inE[2 * got], &inE[2 * got + 1]) != 2) break;
    bestN = n0;
    bestM = got;
    bestE = inE;

    if (d >= 2 && D >= 2 && d <= MAXL) {
        static const int Kc[5] = {1, 1, 2, 2, 3};
        while (!time_up()) {
            int K = Kc[rndint(5)];
            int Gmin = bestN / (2 * K) + 1;   /* 2*K*Gmin > bestN */
            int Gt = Gmin + rndint(3);
            if (Gt < 2) Gt = 2;
            if (Gt > MAXG) break;
            if (!build_group(Gt)) continue;
            k = K;
            G = Gt;
            N = 2 * k * G;
            if (anneal(400000)) {
                int *out = malloc(sizeof(int) * 2 * (size_t)d * k * G);
                emit_lift(out);
                free(bestE);
                bestE = out;
                bestM = d * k * G;
                bestN = N;
            }
            free(mulT); free(invT);
            mulT = NULL; invT = NULL;
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue: safe constructions, then the C search for a larger lift.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        consider(_best_pg(d))
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
    if D >= 4:
        consider(_best_gq(d))

    # Already at the Moore bound: nothing larger exists.
    if best[0] >= lib.moore_bound(d, D):
        return best

    # Let the C engine look for a larger bi-Cayley lift, starting from the incumbent.
    remaining = time_limit - (time.monotonic() - t0)
    budget = 0.8 * remaining - 1.5
    if budget >= 1.0 and d <= 40:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=max(2.0, remaining - 2.0))
            n, e = lib.parse_graph_text(out)
            consider((n, e))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
