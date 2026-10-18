import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define NMAX 2400
#define MAXD 16
#define WMAX 38

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bipartite d-regular graph on N vertices, isA[v] gives the side.
   Search: edge-switch simulated annealing on the number of ordered pairs
   at distance > D. When cost is 0, insert two vertices (matching-based
   insertion keeps regularity) and repair again. */

static int d, D, N, bestN, gen;
static int nb[NMAX * MAXD];
static int bNb[NMAX * MAXD];
static int isA[NMAX], bA[NMAX];
static int mark[NMAX];
static int eu[NMAX * MAXD / 2 + 8], ev[NMAX * MAXD / 2 + 8];
static int deg[NMAX], col[NMAX], qu[NMAX];
static u64 R1[NMAX * WMAX], R2[NMAX * WMAX];

static int has_edge(int a, int b) {
    for (int j = 0; j < d; j++) if (nb[a * d + j] == b) return 1;
    return 0;
}

static int slot_of(int v, int u) {
    for (int j = 0; j < d; j++) if (nb[v * d + j] == u) return j;
    return -1;
}

static long long cost_eval(void) {
    int W = (N + 63) / 64;
    u64 *cur = R1, *nxt = R2;
    size_t tot = (size_t)N * (size_t)W;
    memset(cur, 0, sizeof(u64) * tot);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *s = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int j = 0; j < d; j++) {
                const u64 *s2 = cur + (size_t)nb[v * d + j] * W;
                for (int w = 0; w < W; w++) o[w] |= s2[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < tot; i++) cnt += popc(cur[i]);
    return (long long)N * N - cnt;
}

static void build_complete(void) {
    N = 2 * d;
    for (int v = 0; v < N; v++) isA[v] = (v < d);
    for (int a = 0; a < d; a++)
        for (int j = 0; j < d; j++) {
            nb[a * d + j] = d + j;
            nb[(d + j) * d + a] = a;
        }
}

static int load_start(int n, int m) {
    if (n < 2 || n > NMAX || m <= 0 || m > NMAX * MAXD / 2) return 0;
    for (int i = 0; i < m; i++)
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) return 0;
    if (2 * m != n * d) return 0;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || u >= n || v < 0 || v >= n || u == v) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        nb[u * d + deg[u]++] = v;
        nb[v * d + deg[v]++] = u;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d) return 0;
    /* no duplicate edges */
    for (int u = 0; u < n; u++)
        for (int j = 0; j < d; j++)
            for (int k = j + 1; k < d; k++)
                if (nb[u * d + j] == nb[u * d + k]) return 0;
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int head = 0, tail = 0;
        qu[tail++] = s;
        while (head < tail) {
            int u = qu[head++];
            for (int j = 0; j < d; j++) {
                int w = nb[u * d + j];
                if (col[w] < 0) { col[w] = 1 - col[u]; qu[tail++] = w; }
                else if (col[w] == col[u]) return 0;
            }
        }
    }
    N = n;
    for (int v = 0; v < n; v++) isA[v] = (col[v] == 0);
    return 1;
}

static void save_best(void) {
    bestN = N;
    memcpy(bNb, nb, sizeof(int) * (size_t)N * d);
    memcpy(bA, isA, sizeof(int) * (size_t)N);
}

static void restore_best(void) {
    N = bestN;
    memcpy(nb, bNb, sizeof(int) * (size_t)N * d);
    memcpy(isA, bA, sizeof(int) * (size_t)N);
}

static int pick_side(int A) {
    for (;;) {
        int v = rndi(N);
        if ((isA[v] != 0) == (A != 0)) return v;
    }
}

/* Insert two new vertices (one per side) by removing a matching of d edges
   (a_i, b_i) and wiring a_i to newB and b_i to newA. Degrees stay d. */
static int grow(void) {
    if (N + 2 > NMAX) return 0;
    gen++;
    int px[MAXD], py[MAXD], pj[MAXD], pk[MAXD];
    int cnt = 0;
    for (int tries = 0; cnt < d && tries < 200000; tries++) {
        int x = pick_side(1);
        if (mark[x] == gen) continue;
        int j = rndi(d);
        int y = nb[x * d + j];
        if (mark[y] == gen) continue;
        mark[x] = gen;
        mark[y] = gen;
        px[cnt] = x; py[cnt] = y; pj[cnt] = j; pk[cnt] = slot_of(y, x);
        cnt++;
    }
    if (cnt < d) return 0;
    int na = N, nbv = N + 1;
    isA[na] = 1;
    isA[nbv] = 0;
    mark[na] = 0;
    mark[nbv] = 0;
    N += 2;
    for (int i = 0; i < d; i++) {
        nb[px[i] * d + pj[i]] = nbv;
        nb[py[i] * d + pk[i]] = na;
        nb[na * d + i] = py[i];
        nb[nbv * d + i] = px[i];
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 3 || D < 3 || d > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n = 0, m = 0;
    int loaded = 0;
    if (scanf("%d %d", &n, &m) == 2 && n > 0 && m > 0)
        loaded = load_start(n, m);
    if (!loaded) build_complete();
    if (cost_eval() != 0) build_complete();
    save_best();

    long long curcost = cost_eval();
    int stale = 0;
    long long stagebest = curcost;
    double T0 = 1.0;
    const int PAT = 20000;

    while (now() < tend) {
        if (curcost == 0) {
            if (N > bestN) save_best();
            if (N + 2 > NMAX) break;
            if (!grow()) continue;
            curcost = cost_eval();
            stale = 0;
            stagebest = curcost;
            T0 = 0.02 * (double)curcost;
            if (T0 < 0.5) T0 = 0.5;
            continue;
        }
        if (stale > PAT) {
            restore_best();
            curcost = 0;
            continue;
        }
        double T = T0 * (1.0 - (double)stale / PAT);
        if (T < 0.3) T = 0.3;

        int x1 = pick_side(1), x2 = pick_side(1);
        if (x1 == x2) continue;
        int j1 = rndi(d), j2 = rndi(d);
        int y1 = nb[x1 * d + j1], y2 = nb[x2 * d + j2];
        if (y1 == y2) continue;
        if (has_edge(x1, y2) || has_edge(x2, y1)) continue;
        int s1 = slot_of(y1, x1), s2 = slot_of(y2, x2);
        nb[x1 * d + j1] = y2;
        nb[x2 * d + j2] = y1;
        nb[y1 * d + s1] = x2;
        nb[y2 * d + s2] = x1;
        long long nc = cost_eval();
        if (nc <= curcost || rndu() < exp(-(double)(nc - curcost) / T)) {
            curcost = nc;
            if (curcost < stagebest) { stagebest = curcost; stale = 0; }
            else stale++;
        } else {
            nb[x1 * d + j1] = y1;
            nb[x2 * d + j2] = y2;
            nb[y1 * d + s1] = x1;
            nb[y2 * d + s2] = x2;
            stale++;
        }
    }
    if (curcost == 0 && N > bestN) save_best();

    printf("%d %d\n", bestN, bestN * d / 2);
    for (int v = 0; v < bestN; v++) {
        if (!bA[v]) continue;
        for (int j = 0; j < d; j++) printf("%d %d\n", v, bNb[v * d + j]);
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _is_regular(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    pg = None
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3 or d > 16:
        return best

    # Start the C search from the projective-plane graph when it is d-regular,
    # otherwise from K_{d,d} (the engine handles both).
    start = None
    if pg is not None and _is_regular(pg[0], pg[1], d):
        start = pg

    budget = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=start, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
