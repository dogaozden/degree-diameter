"""Incremental regular-expansion search for bipartite graphs of max degree d and diameter D.

Approach (new in this version, differs from the voltage-lift search):
  1. Start from a d-regular bipartite graph with diameter <= D (PG(2,q) incidence,
     W(q) quadrangle incidence, or K_{d,d}), as an explicit edge list.
  2. Expansion step: remove a matching of d edges and add one new vertex on each side,
     joined so that every degree stays exactly d. This adds one vertex per side.
  3. Repair: simulated annealing over edge switches (a1-b1, a2-b2 -> a1-b2, a2-b1),
     which keep the graph d-regular and bipartite. The cost is the number of ordered
     vertex pairs at distance > D, computed with bitset BFS.
  4. Whenever the cost reaches 0, the state is saved as the new best and the next
     expansion starts from it. Failed attempts are rolled back to the best state.

Python builds the baselines and the start graph, runs the C search, and validates the
result. The fallback is always a valid graph.
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

#define ITERS 20000
#define TEMP0 3.0
#define TEMP1 0.05
#define MAXDEG 64
#define NSCAP 3000

static struct timespec T0s;
static double DEADLINE;
static uint64_t rs[2];

static int DEG, DIAM, NS, E, NSMAX, W;
static int *ea, *eb, *adj, *cnt;
static unsigned char *M, *usedA, *usedB;
static uint64_t *BUF1, *BUF2;
static int have_best = 0, bNS = 0, bE = 0;
static int *bea, *beb;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0s.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0s.tv_nsec);
}

static inline int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Rebuild the adjacency lists from the edge arrays. Vertices: A = 0..NS-1, B = NS..2NS-1. */
static void build_adj(void) {
    int N = 2 * NS;
    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = eb[e] + NS;
        adj[(size_t)a * DEG + cnt[a]++] = b;
        adj[(size_t)b * DEG + cnt[b]++] = a;
    }
}

/* Number of ordered pairs (u, v), u != v, at distance > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int N = 2 * NS;
    W = (N + 63) / 64;
    build_adj();
    uint64_t *c = BUF1, *x = BUF2;
    memset(c, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) c[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = x + (size_t)v * W;
            const uint64_t *cv = c + (size_t)v * W;
            memcpy(o, cv, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int k = 0; k < DEG; k++) {
                const uint64_t *cu = c + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *t = c; c = x; x = t;
    }
    long long unc = 0;
    for (int v = 0; v < N; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += pop64(c[(size_t)v * W + w]);
        unc += N - pc;
    }
    return unc;
}

/* Load the current edge arrays into the adjacency matrix. Returns 0 on a duplicate edge. */
static int load_edges(void) {
    memset(M, 0, (size_t)NSMAX * NSMAX);
    for (int e = 0; e < E; e++) {
        size_t idx = (size_t)ea[e] * NSMAX + eb[e];
        if (M[idx]) return 0;
        M[idx] = 1;
    }
    return 1;
}

static void save_best(void) {
    bNS = NS;
    bE = E;
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
    have_best = 1;
}

static void restore_best(void) {
    NS = bNS;
    E = bE;
    memcpy(ea, bea, sizeof(int) * (size_t)E);
    memcpy(eb, beb, sizeof(int) * (size_t)E);
    load_edges();
}

/* Regular expansion: remove a matching of DEG edges, add one vertex per side.
   Each matched edge (a_k, b_k) becomes (a_k, NA) and a new edge (NA, b_k) is added. */
static int expand(void) {
    if (NS + 1 >= NSMAX) return 0;
    memset(usedA, 0, (size_t)NS);
    memset(usedB, 0, (size_t)NS);
    int ch[MAXDEG];
    int nc = 0;
    long long tries = 0;
    while (nc < DEG && tries < 200000) {
        tries++;
        int e = rnd_int(E);
        int a = ea[e], b = eb[e];
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1;
        usedB[b] = 1;
        ch[nc++] = e;
    }
    if (nc < DEG) return 0;
    int ak[MAXDEG], bk[MAXDEG];
    for (int k = 0; k < DEG; k++) {
        ak[k] = ea[ch[k]];
        bk[k] = eb[ch[k]];
    }
    int NA = NS;
    for (int k = 0; k < DEG; k++) {
        int e = ch[k];
        M[(size_t)ak[k] * NSMAX + bk[k]] = 0;
        eb[e] = NA;
        M[(size_t)ak[k] * NSMAX + NA] = 1;
        ea[E + k] = NA;
        eb[E + k] = bk[k];
        M[(size_t)NA * NSMAX + bk[k]] = 1;
    }
    E += DEG;
    NS += 1;
    return 1;
}

/* Simulated annealing over switches, which preserve regularity and bipartiteness. */
static long long sa_run(int iters) {
    long long cost = eval_cost();
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && elapsed() > DEADLINE) break;
        double p = (double)it / (double)iters;
        double temp = TEMP1 + (TEMP0 - TEMP1) * (1.0 - p);
        int e1 = rnd_int(E), e2 = rnd_int(E);
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (M[(size_t)a1 * NSMAX + b2] || M[(size_t)a2 * NSMAX + b1]) continue;
        M[(size_t)a1 * NSMAX + b1] = 0;
        M[(size_t)a2 * NSMAX + b2] = 0;
        M[(size_t)a1 * NSMAX + b2] = 1;
        M[(size_t)a2 * NSMAX + b1] = 1;
        eb[e1] = b2;
        eb[e2] = b1;
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp((double)(cost - c2) / temp)) {
            cost = c2;
        } else {
            M[(size_t)a1 * NSMAX + b2] = 0;
            M[(size_t)a2 * NSMAX + b1] = 0;
            M[(size_t)a1 * NSMAX + b1] = 1;
            M[(size_t)a2 * NSMAX + b2] = 1;
            eb[e1] = b1;
            eb[e2] = b2;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit   (start graph on stdin)\n");
        return 1;
    }
    timespec_get(&T0s, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n = 0, m = 0;
    if (DEG < 3 || DEG > MAXDEG || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    if (scanf("%d %d", &n, &m) != 2 || m <= 0 || n < 2 || (n & 1) || m != (n / 2) * DEG) {
        printf("0 0\n");
        return 0;
    }
    int NS0 = n / 2;

    double mo = 0, pw = 1;
    for (int i = 0; i < DIAM; i++) {
        mo += pw;
        pw *= (DEG - 1);
        if (pw > 1e9) pw = 1e9;
    }
    NSMAX = (int)mo + 2;
    if (NSMAX > NSCAP) NSMAX = NSCAP;
    if (NSMAX < NS0 + 2) NSMAX = NS0 + 2;

    int EMAX = (NSMAX + 1) * DEG;
    ea = malloc(sizeof(int) * (size_t)EMAX);
    eb = malloc(sizeof(int) * (size_t)EMAX);
    bea = malloc(sizeof(int) * (size_t)EMAX);
    beb = malloc(sizeof(int) * (size_t)EMAX);
    adj = malloc(sizeof(int) * (size_t)2 * NSMAX * DEG);
    cnt = malloc(sizeof(int) * (size_t)2 * NSMAX);
    M = calloc((size_t)NSMAX * NSMAX, 1);
    usedA = calloc((size_t)NSMAX, 1);
    usedB = calloc((size_t)NSMAX, 1);
    int Wmax = (2 * NSMAX + 63) / 64;
    BUF1 = malloc(sizeof(uint64_t) * (size_t)2 * NSMAX * Wmax);
    BUF2 = malloc(sizeof(uint64_t) * (size_t)2 * NSMAX * Wmax);

    /* Read the start graph. Edges may be given in either order. */
    E = m;
    NS = NS0;
    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (u >= NS0) { int t = u; u = v; v = t; }
        if (!(u >= 0 && u < NS0 && v >= NS0 && v < n)) {
            printf("0 0\n");
            return 0;
        }
        ea[i] = u;
        eb[i] = v - NS0;
        deg[u]++;
        deg[v]++;
    }
    for (int v = 0; v < n; v++) {
        if (deg[v] != DEG) {
            printf("0 0\n");
            return 0;
        }
    }
    free(deg);
    if (!load_edges()) {
        printf("0 0\n");
        return 0;
    }

    if (eval_cost() == 0) save_best();

    while (elapsed() < DEADLINE) {
        if (have_best) {
            restore_best();
            if (!expand()) break;
            if (!load_edges()) break;
        }
        long long c = sa_run(ITERS);
        if (c == 0) save_best();
    }

    if (have_best) {
        printf("%d %d\n", 2 * bNS, bE);
        for (int e = 0; e < bE; e++)
            printf("%d %d\n", bea[e], bNS + beb[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Baseline constructions (Python).
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


def _is_regular_split(g, d):
    """True if g is d-regular and every edge joins vertices 0..n/2-1 to n/2..n-1."""
    n, edges = g
    if n < 2 or n % 2:
        return False
    half = n // 2
    deg = [0] * n
    for u, v in edges:
        if not ((u < half <= v) or (v < half <= u)):
            return False
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start_t = time.monotonic()
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start_t < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best
    if d < 3:
        return best

    remaining = 0.9 * time_limit - (time.monotonic() - start_t) - 1.5
    if remaining < 2.0:
        return best

    # The expansion search needs a d-regular, bipartite (side-split) start graph.
    start = best if _is_regular_split(best, d) else lib.haar_graph(d, range(d))

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                        stdin_graph=start, timeout=remaining + 8.0)
        n, e = lib.parse_graph_text(out)
        consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
