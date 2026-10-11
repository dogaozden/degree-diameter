import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parents as safe baselines).
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


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltages of bi-Cayley lifts over the
# semidirect products Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# Base: K vertices per side, DEG layers. Layer l is a permutation of 0..K-1,
# giving darts (l, i) -> B_{dJ[e]} with voltage dS[e]. A_{i,g} ~ B_{j, g*s}.
# Left multiplication is an automorphism, so BFS from the 2K identity
# representatives decides the diameter exactly.
#
# Moves: change a voltage, or swap targets of two darts in one layer (keeps
# degrees). Cost = unreached (rep, vertex) pairs + duplicate-dart penalty.
#
# The engine is a ratchet: it samples (K, group, r) configurations, anneals
# each one, and every success raises the target order for later configurations.
#
# Usage: prog d D seed budget_seconds [min_order]
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define MAXDEG 16
#define MAXK 4
#define MAXNE (MAXDEG * MAXK)

static int DEG, DIAM;
static int K, MM, K2, G, N, NE;
static int POWR[128];
static int dI[MAXNE], dJ[MAXNE], dS[MAXNE];
static int *perm = NULL, *adj = NULL, *cnt = NULL, *fr = NULL, *nx = NULL;
static uint32_t *vis = NULL;
static int capN = 0, capPerm = 0;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int *bestE = NULL;
static int bestN = 0, bestM = 0;

static const int K2_CHOICES[11] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void ensure_cap(int n, int np) {
    if (n > capN) {
        free(adj); free(cnt); free(fr); free(nx); free(vis);
        capN = n + 16;
        adj = malloc(sizeof(int) * (size_t)capN * DEG);
        cnt = malloc(sizeof(int) * (size_t)capN);
        fr = malloc(sizeof(int) * (size_t)capN);
        nx = malloc(sizeof(int) * (size_t)capN);
        vis = calloc((size_t)capN, sizeof(uint32_t));
        stamp = 0;
    }
    if (np > capPerm) {
        free(perm);
        capPerm = np + 16;
        perm = malloc(sizeof(int) * (size_t)capPerm);
    }
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + e) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        vis[src] = stamp;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                const int *au = adj + (size_t)cur[q] * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

static void init_state(void) {
    int p[MAXK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = p[i];
        }
    }
    for (int e = 0; e < NE; e++) {
        dS[e] = rndint(G);
        set_perm(e);
    }
}

/* Returns 1 when a valid lift is in the current state (dS/dJ), 0 otherwise. */
static int anneal_cfg(clock_t t0, double budget, long long max_evals) {
    long long used = 0;
    const int RL = 20000;
    while (used < max_evals) {
        init_state();
        int cur = cost_fn();
        used++;
        if (cur == 0) return 1;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= budget) return 0;
            double T = 2.0 * (1.0 - (double)it / RL) + 0.05;
            used++;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur == 0) return 1;
        }
    }
    return 0;
}

static void record(void) {
    int m = NE * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)m);
    if (!E) return;
    int c = 0;
    for (int e = 0; e < NE; e++) {
        for (int g = 0; g < G; g++) {
            E[2 * c] = dI[e] * G + g;
            E[2 * c + 1] = (K + dJ[e]) * G + perm[(size_t)e * G + g];
            c++;
        }
    }
    free(bestE);
    bestE = E;
    bestM = m;
    bestN = N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    bestN = minN;
    clock_t t0 = clock();

    while (elapsed(t0) < budget) {
        K = 1 + rndint(MAXK);
        int base = bestN / (2 * K);
        int Gt = base + 1 + rndint(base / 8 + 2);
        int k2 = K2_CHOICES[rndint(11)];
        if (k2 > Gt) k2 = 1;
        int m = (Gt + k2 - 1) / k2;
        if (m < 2) m = 2;
        int g_order = m * k2;
        if (g_order < DEG + 1) continue;

        int r = 1;
        if (k2 > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                int c = 2 + rndint(m - 2);
                if (gcd_int(c, m) == 1 && powmod_ll(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
        }

        MM = m;
        K2 = k2;
        G = g_order;
        N = 2 * K * G;
        NE = DEG * K;
        if (N <= bestN) continue;

        POWR[0] = 1 % MM;
        for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);

        ensure_cap(N, NE * G);
        if (!adj || !perm || !vis || !fr || !nx || !cnt) break;

        if (anneal_cfg(t0, budget, 60000)) {
            record();
        }
    }

    if (bestM == 0 || bestE == NULL) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int c = 0; c < bestM; c++) {
        printf("%d %d\n", bestE[2 * c], bestE[2 * c + 1]);
    }
    fflush(stdout);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t_start = time.monotonic()
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

    # Exact constructions first.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Search: one C process ratchets the order upward from the best known order.
    if D >= 3 and 3 <= d <= 12 and time_limit > 8:
        total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
        budget = total - (time.monotonic() - t_start)
        if budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best_n],
                                timeout=budget + 10.0)
                n, e = lib.parse_graph_text(out)
                if n > 0:
                    consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
