import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine A: bi-Cayley lifts over one group (K = 1). Used to build a regular
# start graph quickly. Group Z_m x|_r Z_k2, element (a, b) coded as a*k2 + b.
#
# Usage: prog DEG DIAM m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC (1 << 30)

static int DEG, DIAM, MM, K2, G;
static int *mt, *iv, *POWR, *S, *IS, *bestS, *stampv, *qu;
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d2 = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d2) % K2);
}

static int in_set(int x) {
    for (int t = 0; t < DEG; t++) if (S[t] == x) return 1;
    return 0;
}

static int in_prefix(int x, int upto) {
    for (int t = 0; t < upto; t++) if (S[t] == x) return 1;
    return 0;
}

static void set_inv(void) {
    for (int t = 0; t < DEG; t++) IS[t] = iv[S[t]];
}

static int reach_count(int src) {
    if (stamp >= 0x7ffffff0) {
        memset(stampv, 0, sizeof(int) * (size_t)(2 * G));
        stamp = 0;
    }
    stamp++;
    int head = 0, tail = 0;
    stampv[src] = stamp;
    qu[tail++] = src;
    for (int lv = 0; lv < DIAM && head < tail; lv++) {
        int end = tail;
        while (head < end) {
            int u = qu[head++];
            if (u < G) {
                const int *row = mt + (size_t)u * G;
                for (int t = 0; t < DEG; t++) {
                    int v = G + row[S[t]];
                    if (stampv[v] != stamp) { stampv[v] = stamp; qu[tail++] = v; }
                }
            } else {
                const int *row = mt + (size_t)(u - G) * G;
                for (int t = 0; t < DEG; t++) {
                    int v = row[IS[t]];
                    if (stampv[v] != stamp) { stampv[v] = stamp; qu[tail++] = v; }
                }
            }
        }
    }
    return tail;
}

static int cost_fn(void) {
    int nv = 2 * G;
    return (nv - reach_count(0)) + (nv - reach_count(G));
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (G <= DEG || G > 2400) { printf("0 0\n"); return 0; }

    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }
    {
        int a1 = r, b1 = MM;
        while (b1) { int t = a1 % b1; a1 = b1; b1 = t; }
        if (a1 != 1) { printf("0 0\n"); return 0; }
    }

    mt = malloc(sizeof(int) * (size_t)G * (size_t)G);
    iv = malloc(sizeof(int) * (size_t)G);
    S = malloc(sizeof(int) * (size_t)DEG);
    IS = malloc(sizeof(int) * (size_t)DEG);
    bestS = malloc(sizeof(int) * (size_t)DEG);
    stampv = calloc((size_t)(2 * G), sizeof(int));
    qu = malloc(sizeof(int) * (size_t)(2 * G));
    if (!mt || !iv || !S || !IS || !bestS || !stampv || !qu) { printf("0 0\n"); return 0; }

    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mt[(size_t)x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        iv[x] = 0;
        for (int y = 0; y < G; y++)
            if (mt[(size_t)x * G + y] == 0) { iv[x] = y; break; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int bestCost = BIGC, found = 0;
    const int RL = 30000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGC || rnd01() < 0.3) {
            for (int t = 0; t < DEG; t++) {
                int x;
                do { x = rndint(G); } while (in_prefix(x, t));
                S[t] = x;
            }
            T0 = 3.0;
        } else {
            memcpy(S, bestS, sizeof(int) * (size_t)DEG);
            int kick = 1 + DEG / 3;
            for (int q = 0; q < kick; q++) {
                int t = rndint(DEG);
                int x = rndint(G);
                if (!in_set(x)) S[t] = x;
            }
            T0 = 1.0;
        }
        set_inv();
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.02;
            int t = rndint(DEG);
            int x = rndint(G);
            if (in_set(x)) continue;
            int old = S[t], oldI = IS[t];
            S[t] = x;
            IS[t] = iv[x];
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < bestCost) { bestCost = cur; memcpy(bestS, S, sizeof(int) * (size_t)DEG); }
                if (cur == 0) { found = 1; break; }
            } else {
                S[t] = old;
                IS[t] = oldI;
            }
        }
    }

    if (found) {
        printf("%d %d\n", 2 * G, G * DEG);
        for (int g = 0; g < G; g++)
            for (int t = 0; t < DEG; t++)
                printf("%d %d\n", g, G + mt[(size_t)g * G + S[t]]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Engine B (new, substantially different): grow-and-repair on ARBITRARY
# bipartite graphs, not lifts. Starting from a valid d-regular bipartite graph
# on n vertices, insert a new pair (a in A, b in B) by removing d edges
# (a_i, b_i) with distinct endpoints and adding (a, b_i) and (a_i, b). Degrees
# are preserved exactly. The diameter defect (number of pairs at distance > D)
# is then repaired by simulated annealing over degree-preserving 2-switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Every accepted state is valid, and the
# largest valid graph found is printed.
#
# Usage: prog DEG DIAM seed slice_seconds   (graph on stdin, "n m" + edges)
# ----------------------------------------------------------------------------

GROW_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 4200
#define EMAX 42000
#define DCAP 16
#define WMAX 66

static int DEG, DIAM, N, NE;
static int adjv[NMAX][DCAP], deg[NMAX];
static int eu[EMAX], ev[EMAX];
static int sv_N, sv_NE, sv_deg[NMAX], sv_adj[NMAX][DCAP], sv_eu[EMAX], sv_ev[EMAX];
static uint64_t bufA[NMAX * WMAX], bufB[NMAX * WMAX];
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM (bitset ball propagation). */
static long long cost_fn(void) {
    int n = N, nw = (n + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)nw);
    for (int v = 0; v < n; v++) cur[(size_t)v * nw + v / 64] |= 1ULL << (v % 64);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * nw;
            const uint64_t *c = cur + (size_t)v * nw;
            memcpy(o, c, sizeof(uint64_t) * (size_t)nw);
            for (int t = 0; t < deg[v]; t++) {
                const uint64_t *s = cur + (size_t)adjv[v][t] * nw;
                for (int w = 0; w < nw; w++) o[w] |= s[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long reached = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * nw;
        for (int w = 0; w < nw; w++) reached += popc(c[w]);
    }
    return ((long long)n * n - reached) / 2;
}

static int has_edge(int a, int b) {
    for (int t = 0; t < deg[a]; t++) if (adjv[a][t] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nv) {
    for (int t = 0; t < deg[v]; t++) if (adjv[v][t] == old) { adjv[v][t] = nv; return; }
}

/* Edges i=(a1,b1), j=(a2,b2) become (a1,b2), (a2,b1). Applying it twice undoes it. */
static void do_switch(int i, int j) {
    int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    eu[i] = a1; ev[i] = b2;
    eu[j] = a2; ev[j] = b1;
}

/* Degree-preserving insertion of one A vertex a = N and one B vertex b = N+1. */
static int insert_pair(void) {
    if (N + 2 > NMAX || NE + DEG > EMAX) return 0;
    int pa[DCAP], pb[DCAP], pe[DCAP], k = 0;
    int tries = 0;
    while (k < DEG && tries < 20000) {
        tries++;
        int i = rndint(NE);
        int a = eu[i], b = ev[i], ok = 1;
        for (int t = 0; t < k; t++) if (pa[t] == a || pb[t] == b) { ok = 0; break; }
        if (ok) { pa[k] = a; pb[k] = b; pe[k] = i; k++; }
    }
    if (k < DEG) return 0;
    int a = N, b = N + 1;
    deg[a] = 0; deg[b] = 0;
    for (int t = 0; t < DEG; t++) {
        int i = pe[t], ai = pa[t], bi = pb[t];
        repl(ai, bi, b);
        repl(bi, ai, a);
        eu[i] = a; ev[i] = bi;
        int e = NE++;
        eu[e] = ai; ev[e] = b;
        adjv[a][deg[a]++] = bi;
        adjv[b][deg[b]++] = ai;
    }
    N += 2;
    return 1;
}

static void save_state(void) {
    sv_N = N; sv_NE = NE;
    memcpy(sv_deg, deg, sizeof(deg));
    memcpy(sv_adj, adjv, sizeof(adjv));
    memcpy(sv_eu, eu, sizeof(int) * (size_t)NE);
    memcpy(sv_ev, ev, sizeof(int) * (size_t)NE);
}

static void restore_state(void) {
    N = sv_N; NE = sv_NE;
    memcpy(deg, sv_deg, sizeof(deg));
    memcpy(adjv, sv_adj, sizeof(adjv));
    memcpy(eu, sv_eu, sizeof(int) * (size_t)NE);
    memcpy(ev, sv_ev, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    if (DEG < 1 || DEG > DCAP || DIAM < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || m < 0 || n > NMAX - 2 || m > EMAX - 2 * DEG) {
        printf("0 0\n"); return 0;
    }
    N = n; NE = m;
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= N || v >= N || u == v || deg[u] >= DEG || deg[v] >= DEG) {
            printf("0 0\n"); return 0;
        }
        for (int t = 0; t < deg[u]; t++) if (adjv[u][t] == v) { printf("0 0\n"); return 0; }
        adjv[u][deg[u]++] = v;
        adjv[v][deg[v]++] = u;
        eu[i] = u; ev[i] = v;
    }

    /* Bipartition by BFS; orient every edge so eu is on side 0. */
    int *col = malloc(sizeof(int) * (size_t)N);
    int *st = malloc(sizeof(int) * (size_t)N);
    if (!col || !st) { printf("0 0\n"); return 0; }
    for (int v = 0; v < N; v++) col[v] = -1;
    for (int s = 0; s < N; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int t = 0; t < deg[u]; t++) {
                int w = adjv[u][t];
                if (col[w] < 0) { col[w] = 1 - col[u]; st[sp++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    for (int i = 0; i < NE; i++) {
        if (col[eu[i]] == 1) { int t = eu[i]; eu[i] = ev[i]; ev[i] = t; }
    }

    if (cost_fn() != 0) { printf("0 0\n"); return 0; }
    save_state();

    clock_t t0 = clock();
    int grown = 0;
    while (elapsed(t0) < slice) {
        double rem = slice - elapsed(t0);
        if (rem <= 0.05) break;
        restore_state();
        if (!insert_pair()) break;

        long long cur = cost_fn();
        double asl = rem * 0.5;
        if (asl < 1.0) asl = rem;
        double ta = elapsed(t0);
        const double T0 = 0.6;
        double T = T0;
        int ok = (cur == 0);
        long long it = 0;
        while (!ok) {
            it++;
            if ((it & 31) == 0) {
                double e = elapsed(t0) - ta;
                if (e >= asl) break;
                T = T0 * (1.0 - e / asl) + 0.03;
            }
            int i = rndint(NE), j = rndint(NE);
            if (i == j || eu[i] == eu[j] || ev[i] == ev[j]) continue;
            if (has_edge(eu[i], ev[j]) || has_edge(eu[j], ev[i])) continue;
            do_switch(i, j);
            long long nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur == 0) ok = 1;
            } else {
                do_switch(i, j);
            }
        }
        if (ok) { save_state(); grown++; }
    }

    printf("%d %d\n", sv_N, sv_NE);
    for (int i = 0; i < sv_NE; i++) printf("%d %d\n", sv_eu[i], sv_ev[i]);
    fflush(stdout);
    free(col);
    free(st);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups_of_order(n):
    """All (m, k2, r) with m*k2 == n giving Z_m x|_r Z_k2 (r = 1 is the direct product)."""
    out = []
    for k2 in range(1, n + 1):
        if n % k2:
            continue
        m = n // k2
        if m == 1:
            out.append((1, k2, 1))
        elif k2 == 1:
            out.append((m, 1, 1))
        else:
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    out.append((m, k2, r))
    return out


def _consider(best, n, e, d, D):
    """Return (n, e) if it is a valid strict improvement, else best."""
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


# ----------------------------------------------------------------------------
# Phases.
# ----------------------------------------------------------------------------

def _phase_lift(best, d, D, rng, t_end):
    """Find a large regular bi-Cayley lift to serve as the start graph."""
    while True:
        remaining = t_end - time.monotonic()
        if remaining < 1.5:
            break
        n_lo = best[0] // 2 + 1
        n_grp = max(n_lo + rng.randrange(0, max(4, n_lo // 25)), d + 1)
        if n_grp > 2400:
            break
        opts = _groups_of_order(n_grp)
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        slice_s = min(3.0, remaining)
        try:
            out = lib.run_c(
                BICAY_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        best = _consider(best, n, e, d, D)
    return best


def _phase_grow(best, d, D, seed, t_end):
    """Grow-and-repair from the current best regular graph."""
    remaining = t_end - time.monotonic()
    if remaining < 2.0:
        return best
    try:
        out = lib.run_c(
            GROW_SOURCE,
            [d, D, seed, f"{remaining:.2f}"],
            stdin_graph=best,
            timeout=remaining + 5.0,
        )
    except RuntimeError:
        return best
    try:
        n, e = lib.parse_graph_text(out)
    except ValueError:
        return best
    return _consider(best, n, e, d, D)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _consider(best, pg[0], pg[1], d, D)
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift start (about 45% of the budget).
    if D >= 3 and d >= 3:
        best = _phase_lift(best, d, D, rng, start + 0.45 * budget)

    # Phase 2: grow-and-repair on arbitrary bipartite graphs for the rest.
    if D >= 3:
        best = _phase_grow(best, d, D, rng.randrange(1, 10 ** 9), deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
