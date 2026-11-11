import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

/* Unstructured search: bipartite graphs with parts A (ids 0..N-1) and B (ids HALF..HALF+N-1).
   Start from K_{d,d}. Grow one vertex per side at a time by edge splitting, which keeps the
   graph d-regular, and repair the diameter by double-edge swaps (simulated annealing on the
   number of ordered pairs at distance > D). Every saved graph has cost 0, so it is valid. */

#define HALF 1024
#define MAXV (2 * HALF)
#define WMAX 32
#define MAXDEG 16
#define STALL 3000

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

static int d_, D_, N_;
static int adj[MAXV][MAXDEG];
static int deg[MAXV];
static u64 RA[MAXV * WMAX], RB[MAXV * WMAX];
static int bestAdj[MAXV][MAXDEG];
static int bestDeg[MAXV];
static int bestN = 0;

static inline int PIDX(int u) { return u < HALF ? u : N_ + (u - HALF); }
static inline int IDOF(int p) { return p < N_ ? p : HALF + (p - N_); }

/* Ordered pairs (u, v) at distance > D_. Zero iff the graph is valid. */
static long long evalcost(void) {
    int V = 2 * N_;
    int W = (V + 63) >> 6;
    u64 *cur = RA, *nxt = RB;
    for (int p = 0; p < V; p++) {
        u64 *r = cur + p * WMAX;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[p >> 6] |= 1ULL << (p & 63);
    }
    for (int t = 0; t < D_; t++) {
        for (int p = 0; p < V; p++) {
            int id = IDOF(p);
            u64 *o = nxt + p * WMAX;
            const u64 *c = cur + p * WMAX;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int j = 0; j < deg[id]; j++) {
                const u64 *s = cur + PIDX(adj[id][j]) * WMAX;
                for (int w = 0; w < W; w++) o[w] |= s[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (int p = 0; p < V; p++) {
        const u64 *r = cur + p * WMAX;
        for (int w = 0; w < W; w++) cnt += popc(r[w]);
    }
    return (long long)V * V - cnt;
}

static int has_edge(int a, int b) {
    for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) return 1;
    return 0;
}

static void repl(int v, int from, int to) {
    for (int j = 0; j < deg[v]; j++) if (adj[v][j] == from) { adj[v][j] = to; return; }
}

/* Add one A vertex (id N) and one B vertex (id HALF+N). Each of d edges (a,b) among old
   vertices is split into (a,y) and (b,x). Degrees stay d; the state is always consistent. */
static int grow(void) {
    int Nold = N_;
    if (Nold >= HALF) return 0;
    int x = Nold, y = HALF + Nold;
    deg[x] = 0; deg[y] = 0;
    int done = 0;
    long tries = 0;
    while (done < d_ && tries < 200000) {
        tries++;
        int a = rndi(Nold);
        if (deg[a] == 0) continue;
        int j = rndi(deg[a]);
        int b = adj[a][j];
        if (b >= HALF + Nold) continue;
        if (has_edge(a, y) || has_edge(b, x)) continue;
        adj[a][j] = y;
        repl(b, a, x);
        adj[x][deg[x]++] = b;
        adj[y][deg[y]++] = a;
        done++;
    }
    N_ = Nold + 1;
    return done == d_;
}

static void save_best(void) {
    memcpy(bestAdj, adj, sizeof adj);
    memcpy(bestDeg, deg, sizeof deg);
    bestN = N_;
}

static void restore_best(void) {
    memcpy(adj, bestAdj, sizeof adj);
    memcpy(deg, bestDeg, sizeof deg);
    N_ = bestN;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || d_ > 15 || D_ < 2 || D_ > 50) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    /* Start from K_{d,d} (d-regular, diameter 2). */
    N_ = d_;
    for (int a = 0; a < d_; a++) {
        deg[a] = d_;
        for (int j = 0; j < d_; j++) adj[a][j] = HALF + j;
    }
    for (int b = 0; b < d_; b++) {
        deg[HALF + b] = d_;
        for (int j = 0; j < d_; j++) adj[HALF + b][j] = j;
    }

    long long cost = evalcost();
    const double T = 4.0;
    int stall = 0;
    long long bestc = cost;
    long long iters = 0;

    while (1) {
        if (cost == 0) {
            save_best();
            if (N_ >= HALF - 1) break;
            if (!grow()) { /* state stays consistent; continue searching */ }
            cost = evalcost();
            bestc = cost;
            stall = 0;
            continue;
        }
        iters++;
        if ((iters & 31) == 0 && now() > tend) break;
        stall++;
        if (stall > STALL) {
            restore_best();
            grow();
            cost = evalcost();
            bestc = cost;
            stall = 0;
            continue;
        }

        /* Double-edge swap: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Degrees are preserved. */
        int a1 = rndi(N_), a2 = rndi(N_);
        if (a1 == a2 || deg[a1] == 0 || deg[a2] == 0) continue;
        int j1 = rndi(deg[a1]), j2 = rndi(deg[a2]);
        int b1 = adj[a1][j1], b2 = adj[a2][j2];
        if (b1 == b2 || has_edge(a1, b2) || has_edge(a2, b1)) continue;

        adj[a1][j1] = b2;
        adj[a2][j2] = b1;
        repl(b1, a1, a2);
        repl(b2, a2, a1);
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            adj[a1][j1] = b1;
            adj[a2][j2] = b2;
            repl(b1, a2, a1);
            repl(b2, a1, a2);
        }
        if (cost < bestc) { bestc = cost; stall = 0; }
    }

    /* Output the best saved (valid) graph. A ids 0..n-1, B ids n..2n-1. */
    int n = bestN;
    long long m = 0;
    for (int a = 0; a < n; a++) m += bestDeg[a];
    printf("%d %lld\n", 2 * n, m);
    for (int a = 0; a < n; a++)
        for (int j = 0; j < bestDeg[a]; j++)
            printf("%d %d\n", a, n + (bestAdj[a][j] - HALF));
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or d > 15 or D < 2 or time_limit < 3:
        return best

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
