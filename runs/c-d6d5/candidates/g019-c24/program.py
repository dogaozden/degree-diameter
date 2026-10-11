import time

import lib


# ----------------------------------------------------------------------------
# Growth-and-repair search (a different construction from the lift annealer).
#
# State: a bipartite graph with sides A (side 0) and B (side 1), max degree DEG,
# and a list of edges (ea[e], eb[e]). Only valid states (diameter <= DIAM) are
# kept as the answer.
#
# Growth step: pick DEG edges (a_i, b_i) with pairwise distinct endpoints. Add
# a new A vertex a2 and a new B vertex b2. Replace each (a_i, b_i) by (a_i, b2)
# and add (a2, b_i). Every old degree is unchanged and both new vertices have
# degree DEG, so the graph stays bipartite with max degree DEG and 2 more vertices.
#
# Repair: degree-preserving 2-switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which
# keep bipartiteness. The cost is the number of ordered vertex pairs at distance
# more than DIAM, computed with bitset BFS. Simulated annealing accepts or
# rejects each switch. When the cost reaches 0, the state is saved and grown again.
# When the search stalls, the best valid state is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 6000
#define MAXW ((MAXN + 63) / 64)
#define STALL 80000
#define CHUNK 4000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

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

static int DEG, DIAM, N, E;
static int *adj, *cnt, *side, *ea, *eb, *bea, *beb, *mark, *idxbuf;
static int bestN = 0, bestE = 0;
static int gs = 0;
static uint64_t *bufA, *bufB, *cur, *nxt;

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered pairs (v,u) with dist(v,u) > DIAM. Zero iff the graph is valid. */
static long long eval_cost(void) {
    int W = (N + 63) / 64;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int lvl = 0; lvl < DIAM; lvl++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * (size_t)W);
            const int *av = adj + (size_t)v * DEG;
            for (int k = 0; k < cnt[v]; k++) {
                const uint64_t *u = cur + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) o[w] |= u[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *r = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(r[w]);
        total += N - c;
    }
    return total;
}

static int has_edge(int a, int b) {
    const int *p = adj + (size_t)a * DEG;
    for (int k = 0; k < cnt[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void replace_nb(int v, int old, int nw) {
    int *p = adj + (size_t)v * DEG;
    for (int k = 0; k < cnt[v]; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

/* Edges e1=(x1,y1), e2=(x2,y2) become (x1,y2), (x2,y1). Applying it twice reverts. */
static void do_swap(int e1, int e2) {
    int x1 = ea[e1], y1 = eb[e1], x2 = ea[e2], y2 = eb[e2];
    replace_nb(x1, y1, y2);
    replace_nb(y2, x2, x1);
    replace_nb(x2, y2, y1);
    replace_nb(y1, x1, x2);
    ea[e1] = x1; eb[e1] = y2;
    ea[e2] = x2; eb[e2] = y1;
}

static void save_best(void) {
    bestN = N;
    bestE = E;
    memcpy(bea, ea, sizeof(int) * (size_t)E);
    memcpy(beb, eb, sizeof(int) * (size_t)E);
}

/* Add two vertices by replacing DEG edges with a matching of distinct endpoints. */
static int grow(void) {
    if (E < 1 || N + 2 > MAXN) return 0;
    gs++;
    int nsel = 0;
    long long tries = 0, maxt = 60LL * E + 2000;
    while (nsel < DEG && tries < maxt) {
        tries++;
        int e = rnd_int(E);
        int a = ea[e], b = eb[e];
        if (mark[a] == gs || mark[b] == gs) continue;
        mark[a] = gs;
        mark[b] = gs;
        idxbuf[nsel++] = e;
    }
    if (nsel < DEG) return 0;
    int a2 = N, b2 = N + 1;
    cnt[a2] = 0;
    cnt[b2] = 0;
    side[a2] = 0;
    side[b2] = 1;
    for (int i = 0; i < DEG; i++) {
        int e = idxbuf[i];
        int a = ea[e], b = eb[e];
        replace_nb(a, b, b2);
        replace_nb(b, a, a2);
        eb[e] = b2;
        adj[(size_t)a2 * DEG + cnt[a2]++] = b;
        adj[(size_t)b2 * DEG + cnt[b2]++] = a;
        ea[E] = a2;
        eb[E] = b;
        E++;
    }
    N += 2;
    return 1;
}

static void print_out(void) {
    if (bestN > 0) {
        printf("%d %d\n", bestN, bestE);
        for (int i = 0; i < bestE; i++)
            printf("%d %d\n", bea[i], beb[i]);
    } else {
        printf("0 0\n");
    }
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
    if (DEG < 1 || DEG > 200 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 12345ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 2 || n0 > MAXN || m0 < 1 || m0 > MAXN * DEG) {
        printf("0 0\n");
        return 0;
    }

    size_t MAXE = (size_t)MAXN * DEG + 16;
    adj = malloc(sizeof(int) * (size_t)MAXN * DEG);
    cnt = calloc(MAXN, sizeof(int));
    side = malloc(sizeof(int) * MAXN);
    ea = malloc(sizeof(int) * MAXE);
    eb = malloc(sizeof(int) * MAXE);
    bea = malloc(sizeof(int) * MAXE);
    beb = malloc(sizeof(int) * MAXE);
    mark = calloc(MAXN, sizeof(int));
    idxbuf = malloc(sizeof(int) * (size_t)DEG);
    bufA = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);
    bufB = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);
    cur = bufA;
    nxt = bufB;
    int *tu = malloc(sizeof(int) * (size_t)m0);
    int *tv = malloc(sizeof(int) * (size_t)m0);
    int *queue = malloc(sizeof(int) * (size_t)MAXN);

    int bad = 0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { bad = 1; break; }
        if (cnt[u] >= DEG || cnt[v] >= DEG) { bad = 1; break; }
        adj[(size_t)u * DEG + cnt[u]++] = v;
        adj[(size_t)v * DEG + cnt[v]++] = u;
        tu[i] = u;
        tv[i] = v;
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition by BFS from vertex 0; the graph must be connected and bipartite. */
    N = n0;
    for (int v = 0; v < N; v++) side[v] = -1;
    side[0] = 0;
    int qh = 0, qt = 0;
    queue[qt++] = 0;
    while (qh < qt && !bad) {
        int u = queue[qh++];
        for (int k = 0; k < cnt[u]; k++) {
            int v = adj[(size_t)u * DEG + k];
            if (side[v] < 0) {
                side[v] = 1 - side[u];
                queue[qt++] = v;
            } else if (side[v] == side[u]) {
                bad = 1;
                break;
            }
        }
    }
    for (int v = 0; v < N && !bad; v++)
        if (side[v] < 0) bad = 1;
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    E = 0;
    for (int i = 0; i < m0; i++) {
        int u = tu[i], v = tv[i];
        if (side[u] == 0) { ea[E] = u; eb[E] = v; }
        else { ea[E] = v; eb[E] = u; }
        E++;
    }

    long long cost = eval_cost();
    if (cost == 0) save_best();

    double T = 0.5;
    long long minc = cost;
    long long since = 0;
    long long it = 0;
    while (1) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        it++;
        if (cost == 0) {
            save_best();
            if (!grow()) break;
            cost = eval_cost();
            minc = cost;
            since = 0;
            continue;
        }
        if (it % CHUNK == 0) T = 0.25 + 0.75 * rnd_unit();
        since++;
        if (since > STALL) break;

        int e1 = rnd_int(E), e2 = rnd_int(E);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        do_swap(e1, e2);
        long long nc = eval_cost();
        if (nc <= cost || rnd_unit() < exp(-(double)(nc - cost) / T)) {
            cost = nc;
            if (cost < minc) {
                minc = cost;
                since = 0;
            }
        } else {
            do_swap(e1, e2);
        }
    }

    print_out();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Construction helpers.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: safe baselines in Python, then the C growth-and-repair search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Grow from the best valid start graph. Reserve time for the one-off C
    # compile (outside the C deadline), parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 1.5
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            stdin_graph=best, timeout=remaining + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
