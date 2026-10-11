import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Different search space from the voltage-lift annealer.
#
# The C engine works on an arbitrary d-regular bipartite graph, not a lift.
# It starts from a valid regular graph (a projective-plane or Araujo-Lopez
# graph) and grows it. Growth adds one A-vertex and one B-vertex. Each new
# vertex gets d edges by "splitting" existing edges: remove (x,y), add (x,b)
# and (a,y). Every old vertex keeps its degree, so the graph stays d-regular
# and bipartite.
#
# After each growth step, degree-preserving double-edge swaps (keeping the
# bipartition) are annealed to minimise the number of ordered vertex pairs at
# distance > D. When the cost reaches 0 the graph is saved and grown again.
# The largest saved valid graph is printed. If growth stalls, the C program
# returns the last valid graph it found.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define CAP 4096
#define MW (CAP / 64)
#define ITERS_PER 30000

static int DEG, DIAM, N, NBEST;
static int *adj, *deg, *col, *badj;
static uint64_t *bufA, *bufB;
static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;
static int pa1, pa2, pb1, pb2;

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
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < DEG; i++)
        if (adj[a * DEG + i] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    for (int i = 0; i < DEG; i++)
        if (adj[v * DEG + i] == old) { adj[v * DEG + i] = nw; return; }
}

/* Number of ordered pairs (v,w) with dist(v,w) > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int Wn = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        uint64_t *c = cur + (size_t)v * MW;
        for (int w = 0; w < Wn; w++) c[w] = 0;
        c[v >> 6] |= 1ULL << (v & 63);
    }
    for (int lvl = 0; lvl < DIAM; lvl++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * MW;
            const uint64_t *c = cur + (size_t)v * MW;
            for (int w = 0; w < Wn; w++) o[w] = c[w];
            for (int i = 0; i < DEG; i++) {
                const uint64_t *c2 = cur + (size_t)adj[v * DEG + i] * MW;
                for (int w = 0; w < Wn; w++) o[w] |= c2[w];
            }
            for (int w = 0; w < Wn; w++)
                if (o[w] != c[w]) changed = 1;
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cost = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *c = cur + (size_t)v * MW;
        int cnt = 0;
        for (int w = 0; w < Wn; w++) cnt += popc(c[w]);
        cost += N - cnt;
    }
    return cost;
}

/* Degree-preserving double-edge swap between two A-vertices. Records the move for undo. */
static int propose_swap(void) {
    int a1, a2;
    do { a1 = rnd_int(N); } while (col[a1] != 0);
    do { a2 = rnd_int(N); } while (col[a2] != 0);
    if (a1 == a2) return 0;
    int b1 = adj[a1 * DEG + rnd_int(DEG)];
    int b2 = adj[a2 * DEG + rnd_int(DEG)];
    if (b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    replace_nb(a1, b1, b2);
    replace_nb(a2, b2, b1);
    replace_nb(b1, a1, a2);
    replace_nb(b2, a2, a1);
    pa1 = a1; pa2 = a2; pb1 = b1; pb2 = b2;
    return 1;
}

static void undo_swap(void) {
    replace_nb(pa1, pb2, pb1);
    replace_nb(pa2, pb1, pb2);
    replace_nb(pb1, pa2, pa1);
    replace_nb(pb2, pa1, pa2);
}

static void save_best(void) {
    NBEST = N;
    memcpy(badj, adj, sizeof(int) * (size_t)N * DEG);
}

/* Add a vertex pair (a in A, b in B) and give both degree DEG by edge splitting. */
static int grow(void) {
    if (N + 2 > CAP) return 0;
    int a = N, b = N + 1, old = N;
    N += 2;
    col[a] = 0; col[b] = 1;
    deg[a] = 0; deg[b] = 0;
    long long tries = 0;
    while (deg[a] < DEG && tries < 5000000LL) {
        tries++;
        int x = rnd_int(old);
        if (col[x] != 0) continue;
        int y = adj[x * DEG + rnd_int(DEG)];
        if (y >= old) continue;
        if (has_edge(x, b) || has_edge(y, a)) continue;
        replace_nb(x, y, b);
        replace_nb(y, x, a);
        adj[b * DEG + deg[b]++] = x;
        adj[a * DEG + deg[a]++] = y;
    }
    return deg[a] == DEG && deg[b] == DEG;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    if (DEG < 2 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 2 || n0 > CAP - 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    adj = malloc(sizeof(int) * (size_t)CAP * DEG);
    badj = malloc(sizeof(int) * (size_t)CAP * DEG);
    deg = calloc(CAP, sizeof(int));
    col = malloc(sizeof(int) * CAP);
    bufA = malloc(sizeof(uint64_t) * (size_t)CAP * MW);
    bufB = malloc(sizeof(uint64_t) * (size_t)CAP * MW);

    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v || deg[u] >= DEG || deg[v] >= DEG) {
            bad = 1;
            break;
        }
        adj[u * DEG + deg[u]++] = v;
        adj[v * DEG + deg[v]++] = u;
    }
    for (int v = 0; v < n0 && !bad; v++)
        if (deg[v] != DEG) bad = 1;

    /* Bipartition by BFS (start graph must be connected and bipartite). */
    for (int v = 0; v < n0; v++) col[v] = -1;
    int *qu = malloc(sizeof(int) * (size_t)n0);
    int qh = 0, qt = 0;
    if (!bad) {
        col[0] = 0;
        qu[qt++] = 0;
        while (qh < qt) {
            int v = qu[qh++];
            for (int i = 0; i < DEG; i++) {
                int u = adj[v * DEG + i];
                if (col[u] < 0) { col[u] = 1 - col[v]; qu[qt++] = u; }
                else if (col[u] == col[v]) bad = 1;
            }
        }
        if (qt != n0) bad = 1;
    }
    free(qu);
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    NBEST = 0;
    int stop = 0;
    int iter = 0;
    long long cost = eval_cost();
    if (cost == 0) {
        save_best();
        if (!grow()) stop = 1;
        cost = stop ? 1 : eval_cost();
    }

    while (!stop && elapsed() < DEADLINE) {
        if ((iter & 63) == 0 && elapsed() > DEADLINE) break;
        iter++;
        int ph = iter % ITERS_PER;
        double T = 1.2 * (1.0 - (double)ph / ITERS_PER) + 0.05;
        if (!propose_swap()) continue;
        long long c2 = eval_cost();
        if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            undo_swap();
        }
        if (cost == 0) {
            save_best();
            if (!grow()) { stop = 1; break; }
            cost = eval_cost();
            iter = 0;
        }
    }

    if (NBEST == 0) {
        printf("0 0\n");
        return 0;
    }
    long long m = 0;
    for (int v = 0; v < NBEST; v++)
        if (col[v] == 0)
            for (int i = 0; i < DEG; i++) m++;
    printf("%d %lld\n", NBEST, m);
    for (int v = 0; v < NBEST; v++) {
        if (col[v] != 0) continue;
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", v, badj[v * DEG + i]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Regular bipartite starts (each has every vertex of degree exactly d).
# ----------------------------------------------------------------------------

def _pg_regular(d):
    """Incidence graph of PG(2, d-1), d-regular, diameter 3, when d-1 is a prime power."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for d = q + 2, q a prime power >= 3; d-regular, diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} is d-regular with diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    start_graph = best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for builder in (_pg_regular, _araujo):
            try:
                g = builder(d)
                if g is not None:
                    if g[0] > start_graph[0] and lib.is_valid(g[0], g[1], d, D):
                        start_graph = g
                    consider(g[0], g[1])
            except Exception:
                pass

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    elapsed = time.monotonic() - start
    remaining = 0.85 * time_limit - elapsed - 1.5
    if D >= 2 and remaining >= 1.0:
        hard = min(remaining + 3.0, time_limit - elapsed - 2.0)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=start_graph, timeout=hard)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
