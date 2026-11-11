import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Unstructured search: a d-regular bipartite graph is annealed by double edge swaps
   (which keep degrees and bipartiteness) to minimise the number of pairs at distance > D.
   Once valid, the graph is grown by 2 vertices (one per side) using degree-preserving
   insertion, then annealed again. The largest valid graph seen is printed. */

typedef uint64_t u64;

#define NMAX 1600
#define DMAX 16
#define WMAX ((NMAX + 63) / 64)

static u64 rs = 1;
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

static int d, D, N, W;
static int adj[NMAX * DMAX];
static int deg[NMAX];
static int side[NMAX];
static u64 *R1, *R2;
static int bestadj[NMAX * DMAX];
static int bestside[NMAX];
static int bestN = 0;

static int findslot(int v, int u) {
    for (int j = 0; j < deg[v]; j++)
        if (adj[v * d + j] == u) return j;
    return -1;
}
static int hasedge(int a, int b) { return findslot(a, b) >= 0; }

static void repl(int v, int old, int nw) {
    int j = findslot(v, old);
    if (j >= 0) adj[v * d + j] = nw;
}

/* Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). */
static void doswap(int a1, int b1, int a2, int b2) {
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
}

/* Sum over vertices of pairs at distance > D, divided by 2. */
static long long cost_eval(void) {
    W = (N + 63) / 64;
    memset(R1, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) R1[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = R2 + (size_t)v * W;
            u64 *s = R1 + (size_t)v * W;
            memcpy(o, s, sizeof(u64) * (size_t)W);
            for (int j = 0; j < deg[v]; j++) {
                int u = adj[v * d + j];
                u64 *p = R1 + (size_t)u * W;
                for (int w = 0; w < W; w++) o[w] |= p[w];
            }
        }
        u64 *tmp = R1; R1 = R2; R2 = tmp;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(R1[(size_t)v * W + w]);
        unr += N - c;
    }
    return unr / 2;
}

/* Returns 1 if a valid graph is reached within maxit moves, 0 otherwise (or on timeout). */
static int anneal(double tend, long long maxit, double T) {
    long long c = cost_eval();
    for (long long it = 0; it < maxit && c > 0; it++) {
        if ((it & 255) == 0 && now() > tend) return 0;
        int a1 = rndi(N);
        if (side[a1] != 0) continue;
        int a2 = rndi(N);
        if (side[a2] != 0 || a2 == a1) continue;
        int b1 = adj[a1 * d + rndi(d)];
        int b2 = adj[a2 * d + rndi(d)];
        if (b1 == b2) continue;
        if (hasedge(a1, b2) || hasedge(a2, b1)) continue;
        doswap(a1, b1, a2, b2);
        long long c2 = cost_eval();
        if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) {
            c = c2;
        } else {
            doswap(a1, b2, a2, b1);
        }
    }
    return c == 0;
}

/* Add vertices a (side A) and b (side B). Take d edges (x_i,y_i) with distinct x's and
   distinct y's, replace them by (x_i,b) and (a,y_i). All degrees stay d. */
static int insert_pair(void) {
    if (N + 2 > NMAX) return 0;
    int xs[DMAX], ys[DMAX];
    int cnt = 0;
    long long tries = 0;
    while (cnt < d && tries < 200000) {
        tries++;
        int x = rndi(N);
        if (side[x] != 0 || deg[x] != d) continue;
        int y = adj[x * d + rndi(d)];
        int ok = 1;
        for (int i = 0; i < cnt; i++)
            if (xs[i] == x || ys[i] == y) { ok = 0; break; }
        if (!ok) continue;
        xs[cnt] = x;
        ys[cnt] = y;
        cnt++;
    }
    if (cnt < d) return 0;
    int a = N, b = N + 1;
    N += 2;
    side[a] = 0; side[b] = 1;
    deg[a] = 0; deg[b] = 0;
    for (int i = 0; i < d; i++) {
        int x = xs[i], y = ys[i];
        repl(x, y, b);
        repl(y, x, a);
        adj[a * d + deg[a]++] = y;
        adj[b * d + deg[b]++] = x;
    }
    return 1;
}

/* Random d-regular bipartite graph with s vertices per side (union of d random matchings). */
static int build_random(int s) {
    N = 2 * s;
    for (int v = 0; v < N; v++) {
        deg[v] = 0;
        side[v] = v >= s;
    }
    static int p[NMAX];
    for (int l = 0; l < d; l++) {
        int tries = 0, placed = 0;
        while (!placed) {
            for (int i = 0; i < s; i++) p[i] = i;
            for (int i = s - 1; i > 0; i--) {
                int j = rndi(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            int ok = 1;
            for (int i = 0; i < s && ok; i++)
                if (hasedge(i, s + p[i])) ok = 0;
            if (ok) {
                for (int i = 0; i < s; i++) {
                    int b = s + p[i];
                    adj[i * d + deg[i]++] = b;
                    adj[b * d + deg[b]++] = i;
                }
                placed = 1;
            } else if (++tries > 100000) {
                return 0;
            }
        }
    }
    return 1;
}

static void snapshot(void) {
    bestN = N;
    memcpy(bestadj, adj, sizeof(int) * (size_t)N * d);
    memcpy(bestside, side, sizeof(int) * (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int s0 = atoi(argv[5]);
    if (d < 3 || d > DMAX || D < 3) { printf("0 0\n"); return 0; }
    if (s0 < d) s0 = d;
    if (2 * s0 > NMAX - 2) s0 = (NMAX - 2) / 2;

    rs = (u64)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    R1 = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    R2 = malloc(sizeof(u64) * (size_t)NMAX * WMAX);
    if (!R1 || !R2) { printf("0 0\n"); return 0; }

    double tend = now() + tl;
    if (!build_random(s0)) { printf("0 0\n"); return 0; }

    int fails = 0;
    while (now() < tend) {
        double Ts[3] = {0.35, 0.7, 1.2};
        double T = Ts[rndi(3)];
        if (anneal(tend, 40000, T)) {
            fails = 0;
            if (N > bestN) snapshot();
            if (!insert_pair()) break;
        } else {
            if (++fails >= 4) break;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    int m = 0;
    for (int v = 0; v < bestN; v++)
        if (bestside[v] == 0) m += d;
    printf("%d %d\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        if (bestside[v] == 0)
            for (int j = 0; j < d; j++)
                printf("%d %d\n", v, bestadj[v * d + j]);
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

    if d < 3 or D < 3:
        return best

    budget = max(0.5, time_limit - 6.0)
    # Start the annealer from a random d-regular bipartite graph of about the fallback size.
    s0 = max(d, best_n // 2)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), s0],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
