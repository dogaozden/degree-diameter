import lib


# Engine: start from a valid graph on stdin and grow it by two vertices at a time.
# Each growth step adds one new A-vertex and one new B-vertex, rewires d matching
# edges through them (keeping all degrees and bipartiteness), then runs simulated
# annealing with degree-preserving double-edge swaps to drive the number of
# unreached ordered pairs (distance > D) to zero. Every success becomes the new base.
C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXV 2048
#define MAXD 16
#define WMAX (MAXV / 64)
#define ECAP 20000
#define MAXIN 20000

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

typedef struct {
    int n, m;
    int deg[MAXV];
    int nb[MAXV][MAXD];
    int col[MAXV];      /* 0 = A side, 1 = B side */
    int EA[ECAP];       /* edge e joins EA[e] (side 0) and EB[e] (side 1) */
    int EB[ECAP];
} St;

static St G, BASE, BEST;
static int d_, D_;
static u64 BUF0[MAXV * WMAX], BUF1[MAXV * WMAX];
static int IU[MAXIN], IV[MAXIN];

static void rep(int v, int old, int nw) {
    for (int i = 0; i < G.deg[v]; i++)
        if (G.nb[v][i] == old) { G.nb[v][i] = nw; return; }
}

static int has_edge(int a, int b) {
    for (int i = 0; i < G.deg[a]; i++)
        if (G.nb[a][i] == b) return 1;
    return 0;
}

/* Edges i=(a1,b1), j=(a2,b2) become (a1,b2), (a2,b1). Applying twice restores. */
static void doswap(int i, int j) {
    int a1 = G.EA[i], b1 = G.EB[i], a2 = G.EA[j], b2 = G.EB[j];
    rep(a1, b1, b2);
    rep(b1, a1, a2);
    rep(a2, b2, b1);
    rep(b2, a2, a1);
    G.EB[i] = b2;
    G.EB[j] = b1;
}

/* Number of ordered pairs (v, w) with distance > D_ (0 means valid diameter). */
static long long cost_eval(void) {
    int n = G.n, W = (n + 63) / 64;
    u64 *cur = BUF0, *nxt = BUF1;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *o = nxt + (size_t)v * W;
            const u64 *c = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = c[w];
            for (int i = 0; i < G.deg[v]; i++) {
                const u64 *c2 = cur + (size_t)G.nb[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= c2[w];
            }
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long cnt = 0;
    for (size_t k = 0; k < (size_t)n * W; k++) cnt += popc(cur[k]);
    return (long long)n * n - cnt;
}

/* Add two vertices a (side 0) and b (side 1). Choose d edges with distinct
   endpoints; move each chosen edge (x,y) to (a,y) and add (x,b). Degrees of
   all old vertices are unchanged, and a, b end with degree d. */
static int grow(void) {
    int n = G.n, d = d_;
    if (n + 2 > MAXV || G.m + d > ECAP) return 0;
    static char uA[MAXV], uB[MAXV];
    memset(uA, 0, sizeof uA);
    memset(uB, 0, sizeof uB);
    int chosen[MAXD];
    int k = 0;
    for (int tries = 0; k < d && tries < 200000; tries++) {
        int e = rndi(G.m);
        int x = G.EA[e], y = G.EB[e];
        if (uA[x] || uB[y]) continue;
        uA[x] = 1; uB[y] = 1;
        chosen[k++] = e;
    }
    if (k < d) return 0;
    int a = n, b = n + 1;
    G.col[a] = 0; G.col[b] = 1;
    G.deg[a] = 0; G.deg[b] = 0;
    for (int q = 0; q < d; q++) {
        int e = chosen[q];
        int x = G.EA[e], y = G.EB[e];
        G.EA[e] = a; G.EB[e] = y;
        rep(x, y, b);
        rep(y, x, a);
        G.nb[a][G.deg[a]++] = y;
        G.nb[b][G.deg[b]++] = x;
        G.EA[G.m] = x; G.EB[G.m] = b;
        G.m++;
    }
    G.n = n + 2;
    return 1;
}

/* Simulated annealing on degree-preserving double-edge swaps. Returns final cost. */
static long long anneal(int iters, double tend, double T0) {
    long long cur = cost_eval();
    for (int t = 0; t < iters && cur > 0; t++) {
        if ((t & 31) == 0 && now() > tend) break;
        double T = T0 * (1.0 - (double)t / iters) + 0.05;
        int i = rndi(G.m), j = rndi(G.m);
        if (i == j) continue;
        int a1 = G.EA[i], b1 = G.EB[i], a2 = G.EA[j], b2 = G.EB[j];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        doswap(i, j);
        long long c2 = cost_eval();
        if (c2 <= cur || rndu() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
        } else {
            doswap(i, j);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
    if (n <= 0 || n > MAXV - 2 || m < 0 || m > MAXIN) { printf("0 0\n"); return 0; }
    memset(&G, 0, sizeof G);
    G.n = n;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { printf("0 0\n"); return 0; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { printf("0 0\n"); return 0; }
        if (G.deg[u] >= d_ || G.deg[v] >= d_) { printf("0 0\n"); return 0; }
        G.nb[u][G.deg[u]++] = v;
        G.nb[v][G.deg[v]++] = u;
        IU[e] = u; IV[e] = v;
    }
    /* Bipartition by BFS colouring. */
    for (int v = 0; v < n; v++) G.col[v] = -1;
    static int q[MAXV];
    for (int s = 0; s < n; s++) {
        if (G.col[s] >= 0) continue;
        G.col[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < G.deg[u]; i++) {
                int w = G.nb[u][i];
                if (G.col[w] < 0) { G.col[w] = 1 - G.col[u]; q[tail++] = w; }
                else if (G.col[w] == G.col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }
    for (int e = 0; e < m; e++) {
        if (G.col[IU[e]] == 0) { G.EA[e] = IU[e]; G.EB[e] = IV[e]; }
        else { G.EA[e] = IV[e]; G.EB[e] = IU[e]; }
    }
    G.m = m;

    if (cost_eval() != 0) { printf("0 0\n"); return 0; }
    BEST = G;
    BASE = G;

    int fails = 0;
    while (now() < tend) {
        G = BASE;
        if (!grow()) { fails++; continue; }
        int iters = 3000 + 200 * (fails < 25 ? fails : 25);
        long long c = anneal(iters, tend, 3.0);
        if (c == 0) {
            BASE = G;
            BEST = G;
            fails = 0;
        } else {
            fails++;
        }
    }

    printf("%d %d\n", BEST.n, BEST.m);
    for (int e = 0; e < BEST.m; e++)
        printf("%d %d\n", BEST.EA[e], BEST.EB[e]);
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum

    if d < 3 or D < 3:
        return best

    # Grow the best valid start graph inside the single C run.
    budget = max(0.5, time_limit - 6.0)
    try:
        out = lib.run_c(C_GROW, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
