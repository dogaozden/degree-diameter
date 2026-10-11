import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: simulated annealing over voltages of a bi-Cayley lift over
# Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b). Cost is the excess
# distance over all representatives; zero means the lift has diameter <= DIAM.
#
# Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
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

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
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

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
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
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
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
            if (cur < bestCost) { bestCost = cur; save_best(); }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new, different in kind): graph-level repair annealing.
# Input: a bipartite graph (side-0 / side-1 found by BFS), max degree d.
# Moves: edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). These keep every
# degree and the bipartition. Cost = number of unordered pairs at distance
# > DIAM, computed exactly with bitset BFS (one bitset per vertex).
# Usage: prog d D seed slice_seconds ; prints a valid graph or "0 0".
# ----------------------------------------------------------------------------

C_REPAIR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int N, E, DEG, DIAM, W;
static int *ea, *eb, *adj, *dg, *side, *bA, *bB;
static uint64_t *R0, *R1;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int x, int y) {
    for (int k = 0; k < dg[x]; k++) if (adj[(size_t)x * DEG + k] == y) return 1;
    return 0;
}

static void repl(int x, int old, int nw) {
    for (int k = 0; k < dg[x]; k++) {
        if (adj[(size_t)x * DEG + k] == old) { adj[(size_t)x * DEG + k] = nw; return; }
    }
}

/* Replace edges e1=(a1,b1), e2=(a2,b2) by (a1,b2), (a2,b1). Self-inverse
   when applied to the resulting edges. Returns 0 if it would break simplicity. */
static int do_switch(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    if (e1 == e2 || a1 == a2 || b1 == b2) return 0;
    if (has(a1, b2) || has(a2, b1)) return 0;
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    eb[e1] = b2;
    eb[e2] = b1;
    return 1;
}

/* Number of unordered pairs at distance > DIAM. */
static long cost(void) {
    uint64_t *cur = R0, *nxt = R1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int lv = 0; lv < DIAM; lv++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *src = cur + (size_t)adj[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long c = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        const uint64_t *r = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) pc += popc(r[w]);
        c += N - pc;
    }
    return c / 2;
}

static void save_best(void) {
    memcpy(bA, ea, sizeof(int) * (size_t)E);
    memcpy(bB, eb, sizeof(int) * (size_t)E);
}

static void fail(void) { printf("0 0\n"); exit(0); }

int main(int argc, char **argv) {
    if (argc < 5) fail();
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;
    if (DEG < 1 || DIAM < 1) fail();
    if (scanf("%d %d", &N, &E) != 2 || N < 1 || E < 1) fail();

    ea = malloc(sizeof(int) * E);
    eb = malloc(sizeof(int) * E);
    bA = malloc(sizeof(int) * E);
    bB = malloc(sizeof(int) * E);
    side = malloc(sizeof(int) * N);
    dg = calloc(N, sizeof(int));
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    int *queue = malloc(sizeof(int) * N);
    if (!ea || !eb || !bA || !bB || !side || !dg || !adj || !queue) fail();

    for (int e = 0; e < E; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) fail();
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) fail();
        if (dg[u] >= DEG || dg[v] >= DEG) fail();
        if (has(u, v)) fail();
        adj[(size_t)u * DEG + dg[u]++] = v;
        adj[(size_t)v * DEG + dg[v]++] = u;
        ea[e] = u;
        eb[e] = v;
    }

    /* Bipartition by BFS. */
    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int k = 0; k < dg[u]; k++) {
                int v = adj[(size_t)u * DEG + k];
                if (side[v] < 0) { side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) fail();
            }
        }
    }
    /* Orient each edge so ea is on side 0. */
    for (int e = 0; e < E; e++) {
        if (side[ea[e]] != 0) { int t = ea[e]; ea[e] = eb[e]; eb[e] = t; }
    }

    W = (N + 63) / 64;
    R0 = malloc(sizeof(uint64_t) * (size_t)N * W);
    R1 = malloc(sizeof(uint64_t) * (size_t)N * W);
    if (!R0 || !R1) fail();

    long cur = cost();
    long bestc = cur;
    save_best();

    clock_t t0 = clock();
    const double T0 = 1.5;
    while (cur > 0) {
        double el = (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
        if (el >= slice) break;
        double T = T0 * (1.0 - el / slice) + 0.03;
        int e1 = rndint(E), e2 = rndint(E);
        if (e1 == e2) continue;
        if (!do_switch(e1, e2)) continue;
        long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur < bestc) { bestc = cur; save_best(); }
        } else {
            do_switch(e1, e2);
        }
    }

    if (bestc == 0) {
        printf("%d %d\n", N, E);
        for (int e = 0; e < E; e++) printf("%d %d\n", bA[e], bB[e]);
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions and helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _two_colour(n, edges):
    """Return a 0/1 side label per vertex (bipartition), or None if not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


K2_CHOICES = [1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 21, 24,
              27, 28, 30, 36, 40, 42, 49, 54, 56, 63, 72, 81, 84, 96, 108, 121,
              128, 162, 243]


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice(K2_CHOICES)
        m0 = max(2, -(-target // k2))
        for m in range(m0, m0 + 40):
            if k2 == 1:
                return m, 1, 1
            nontrivial = [c for c in range(2, m)
                          if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if nontrivial:
                return m, k2, rng.choice(nontrivial)
            return m, k2, 1
    return None


# ----------------------------------------------------------------------------
# Growth by pair insertion followed by C repair.
# Insert a fresh pair (A, B) with edge A-B. Remove d-1 vertex-disjoint edges
# (a_i, b_i); join A to every b_i and B to every a_i. Degrees are preserved
# and the bipartition is kept. The graph is then larger and may be invalid;
# the C repair anneals it back to diameter <= D or reports failure.
# ----------------------------------------------------------------------------

def _insert_pairs(n, edges, col, d, k, rng):
    """Insert k fresh pairs. Returns (n, edges, col) or None if no room."""
    edges = list(edges)
    col = list(col)
    for _ in range(k):
        order = list(range(len(edges)))
        rng.shuffle(order)
        used = set()
        picked = []
        for idx in order:
            u, v = edges[idx]
            a, b = (u, v) if col[u] == 0 else (v, u)
            if a in used or b in used:
                continue
            used.add(a)
            used.add(b)
            picked.append((idx, a, b))
            if len(picked) == d - 1:
                break
        if len(picked) < d - 1:
            return None
        drop = {idx for idx, _, _ in picked}
        A, B = n, n + 1
        new = [(A, B)] + [(A, b) for _, _, b in picked] + [(a, B) for _, a, _ in picked]
        edges = [edges[i] for i in range(len(edges)) if i not in drop] + new
        col += [0, 1]
        n += 2
    return n, edges, col


def _grow(best, d, D, rng, end):
    """Repeatedly insert pairs and repair with C annealing until `end`. Returns a valid graph."""
    n, edges = best
    col = _two_colour(n, edges)
    if col is None or d < 3:
        return best
    pairs = 1
    while True:
        remaining = end - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(remaining - 1.0, 5.0)
        cand = _insert_pairs(n, edges, col, d, pairs, rng)
        if cand is None:
            break
        cn, ce, _ = cand
        try:
            out = lib.run_c(
                C_REPAIR,
                [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(cn, ce),
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n2, e2 = lib.parse_graph_text(out)
        except ValueError:
            n2, e2 = 0, []
        if n2 == cn and lib.is_valid(n2, e2, d, D):
            n, edges = n2, e2
            col = _two_colour(n, edges)
            if col is None:
                break
            pairs = min(pairs * 2, 16)
        else:
            pairs = max(1, pairs // 2)
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    lift_end = start + 0.45 * budget
    grow_end = start + 0.93 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: lift search (annealing over voltages of a bi-Cayley lift).
    step = 0.08
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
        k = rng.choice([1, 1, 2, 2, 3])
        want = best[0] * (1.0 + step)
        target = max(2, math.ceil(want / (2 * k)))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_LIFT,
                [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            step = max(0.005, step * 0.7)
            continue
        if consider(n, e):
            step = min(0.4, step * 1.25)
        else:
            step = max(0.005, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Phase 2: grow the best graph by pair insertion and graph-level repair.
    try:
        n2, e2 = _grow(best, d, D, rng, grow_end)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
