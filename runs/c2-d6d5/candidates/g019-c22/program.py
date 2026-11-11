import lib


# Bold change: this engine no longer lifts block-darts over Z_m x| Z_k. It searches
# bi-Cayley graphs instead. One group G (order 2 = |G| side vertices ... i.e. A_x and B_y
# for x, y in G) and a connection set S of d distinct group elements give the edges
# A_x ~ B_{x s} for s in S. Such a graph is d-regular and bipartite, and it is
# vertex-transitive on each side, so diameter <= D reduces to two BFS runs (from A_e and
# from B_e). That makes each cost evaluation cheap, so annealing can run many moves.
# Groups are random Z_m x| Z_k2 (with a random valid r, or r = 1 for direct products),
# with |G| just above the current best order. Any failure falls back to the safe graphs.

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define GMAX 1200
#define SPAN 24
#define ITERS 60000

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

static int d_, D_, G_, minG_;
static int MT[GMAX * GMAX];
static int INV[GMAX];
static int S[MAXD], SI[MAXD];
static int adjv[2 * GMAX * MAXD];
static int distv[2 * GMAX];
static int queue_[2 * GMAX];
static int pw[GMAX];
static int divs[GMAX];
static int cand[GMAX];
static int bestG = 0, bEc = 0;
static int bE[2 * GMAX * MAXD];

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element a*k2 + b. */
static void build_group(int m, int k2, int r) {
    int G = m * k2;
    G_ = G;
    pw[0] = 1 % m;
    for (int t = 1; t < k2; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++) INV[x] = 0;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) INV[x] = y;
}

static int inS(int g, int upto) {
    for (int l = 0; l < upto; l++) if (S[l] == g) return 1;
    return 0;
}

/* Set connection element of column l to g and refresh adjacency for that column.
   A_x (index x) ~ B_{x g} (index G + x g); B_y (index G + y) ~ A_{y g^{-1}}. */
static void setS(int l, int g) {
    int G = G_, d = d_;
    S[l] = g;
    SI[l] = INV[g];
    for (int x = 0; x < G; x++) {
        adjv[(size_t)x * d + l] = G + MT[x * G + g];
        adjv[(size_t)(G + x) * d + l] = MT[x * G + SI[l]];
    }
}

static int bfs_count(int src) {
    int N = 2 * G_, d = d_;
    for (int v = 0; v < N; v++) distv[v] = -1;
    int qh = 0, qt = 0, cnt = 1;
    distv[src] = 0;
    queue_[qt++] = src;
    while (qh < qt) {
        int v = queue_[qh++];
        if (distv[v] >= D_) continue;
        const int *row = adjv + (size_t)v * d;
        for (int l = 0; l < d; l++) {
            int u = row[l];
            if (distv[u] < 0) {
                distv[u] = distv[v] + 1;
                queue_[qt++] = u;
                cnt++;
            }
        }
    }
    return cnt;
}

/* Zero iff every pair is within distance D (vertex-transitivity on each side). */
static long long cost(void) {
    int N = 2 * G_;
    return (long long)(2 * N - bfs_count(0) - bfs_count(G_));
}

/* Returns 1 if a valid connection set is found, 0 if not within iters, -1 on timeout. */
static int anneal(double tend, int iters) {
    int G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        int g;
        do { g = rndi(G); } while (inS(g, l));
        S[l] = g;
    }
    for (int l = 0; l < d; l++) setS(l, S[l]);
    long long c = cost();
    if (c == 0) return 1;
    double T0 = 2.0, T1 = 0.03;
    for (int t = 0; t < iters; t++) {
        if ((t & 255) == 0 && now() > tend) return -1;
        double frac = (double)t / (double)iters;
        double T = T0 * pow(T1 / T0, frac);
        int l = rndi(d);
        int g;
        do { g = rndi(G); } while (inS(g, d));
        int old = S[l];
        setS(l, g);
        long long c2 = cost();
        if (c2 <= c || rndu() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c == 0) return 1;
        } else {
            setS(l, old);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    /* Vertices = 2|G|, so |G| >= ceil(minN / 2); also need |G| > d. */
    minG_ = (minN + 1) / 2;
    if (minG_ < d_ + 1) minG_ = d_ + 1;

    while (now() < tend) {
        if (minG_ > GMAX) break;
        int G = minG_ + rndi(SPAN);
        if (G > GMAX) G = GMAX;

        int nd = 0;
        for (int k2 = 1; k2 <= G; k2++)
            if (G % k2 == 0 && G / k2 >= 2) divs[nd++] = k2;
        if (nd == 0) continue;
        int k2 = divs[rndi(nd)];
        int m = G / k2;

        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = (rndu() < 0.5) ? 1 : cand[rndi(nc)];

        build_group(m, k2, r);
        int st = anneal(tend, ITERS);
        if (st < 0) break;
        if (st == 1) {
            if (G > bestG) {
                bestG = G;
                bEc = 0;
                for (int x = 0; x < G; x++)
                    for (int l = 0; l < d_; l++) {
                        bE[2 * bEc] = x;
                        bE[2 * bEc + 1] = G + MT[x * G + S[l]];
                        bEc++;
                    }
            }
            if (G + 1 > minG_) minG_ = G + 1;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bEc);
    for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
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

    # Leave a reserve for compilation (not counted by the subprocess timeout),
    # Python glue and output parsing.
    budget = max(0.5, time_limit - 6.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
