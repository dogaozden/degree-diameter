import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 16
#define HMAX 1000
#define WMAX ((2 * HMAX + 63) / 64)

/* Unstructured search: each layer l is a permutation perm[l] between
   A-vertices 0..h-1 and B-vertices 0..h-1. Edge A_a ~ B_{perm[l][a]} for every l,
   so the graph is d-regular bipartite on 2h vertices. Cost = ordered unreachable
   pairs within distance D, plus a heavy penalty for parallel edges.
   Search grows h adaptively, rolls back to the last valid graph on stagnation. */

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

static int d_, D_, h_, W_, hcap;
static int perm[MAXD][HMAX], inv_[MAXD][HMAX];
static int bperm[MAXD][HMAX], bh = 0;
static u64 RA[2 * HMAX * WMAX], RB[2 * HMAX * WMAX];

static inline int nbr(int v, int l) {
    int h = h_;
    return v < h ? h + perm[l][v] : inv_[l][v - h];
}

static long long evalcost(void) {
    int h = h_, d = d_, W = W_, n = 2 * h;
    u64 *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(u64) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *out = nxt + (size_t)v * W;
            const u64 *self = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) out[w] = self[w];
            for (int l = 0; l < d; l++) {
                const u64 *src = cur + (size_t)nbr(v, l) * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        u64 *sw = cur; cur = nxt; nxt = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)n * (size_t)W; i++) cnt += popc(cur[i]);
    long long unreached = (long long)n * n - cnt;
    long long dup = 0;
    for (int a = 0; a < h; a++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (perm[l][a] == perm[l2][a]) dup++;
    return unreached + 1000 * dup;
}

static void random_init(int h) {
    h_ = h;
    W_ = (2 * h + 63) / 64;
    for (int l = 0; l < d_; l++) {
        for (int a = 0; a < h; a++) perm[l][a] = a;
        for (int i = h - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = t;
        }
        for (int a = 0; a < h; a++) inv_[l][perm[l][a]] = a;
    }
}

/* Add one A-vertex and one B-vertex. In each layer, a random old A-vertex
   a gives its target t to the new A-vertex, and a points to the new B-vertex. */
static void grow1(void) {
    int h = h_;
    for (int l = 0; l < d_; l++) {
        int a = rndi(h);
        int t = perm[l][a];
        perm[l][h] = t; inv_[l][t] = h;
        perm[l][a] = h; inv_[l][h] = a;
    }
    h_ = h + 1;
    W_ = (2 * h_ + 63) / 64;
}

static void snapshot(void) {
    bh = h_;
    for (int l = 0; l < d_; l++)
        memcpy(bperm[l], perm[l], sizeof(int) * (size_t)h_);
}

static void restore(void) {
    h_ = bh;
    W_ = (2 * h_ + 63) / 64;
    for (int l = 0; l < d_; l++)
        for (int a = 0; a < h_; a++) {
            perm[l][a] = bperm[l][a];
            inv_[l][perm[l][a]] = a;
        }
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

    /* Moore bound: n <= 2M with M = sum_{i<D} (d-1)^i, so the half order h <= M. */
    double M = 0, pw = 1;
    for (int i = 0; i < D_; i++) {
        M += pw;
        pw *= (d_ - 1);
        if (M > 1e7) break;
    }
    hcap = M > HMAX ? HMAX : (int)M;
    if (hcap < d_) { printf("0 0\n"); return 0; }

    int h = d_;
    random_init(h);
    int step = h / 16 >= 1 ? h / 16 : 1;
    long long cost = evalcost();
    long long bestc = cost;
    long long stall = 0, iter = 0;

    while (1) {
        if (cost == 0) {
            snapshot();
            if (h_ >= hcap) break;
            for (int s = 0; s < step && h_ < hcap; s++) grow1();
            step = h_ / 16 >= 1 ? h_ / 16 : 1;
            cost = evalcost();
            bestc = cost;
            stall = 0;
            continue;
        }
        if ((iter & 127) == 0 && now() > tend) break;
        iter++;

        double temp = 0.3 + 0.02 * (double)cost;
        int l = rndi(d_);
        int a1 = rndi(h_), a2 = rndi(h_ - 1);
        if (a2 >= a1) a2++;
        int t1 = perm[l][a1], t2 = perm[l][a2];
        perm[l][a1] = t2; perm[l][a2] = t1;
        inv_[l][t2] = a1; inv_[l][t1] = a2;
        long long c2 = evalcost();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            perm[l][a1] = t1; perm[l][a2] = t2;
            inv_[l][t1] = a1; inv_[l][t2] = a2;
        }

        if (cost < bestc) { bestc = cost; stall = 0; }
        else stall++;

        if (stall > 2000 + 8LL * h_) {
            if (bh > 0) {
                restore();
                step = step / 2 >= 1 ? step / 2 : 1;
                for (int s = 0; s < step && h_ < hcap; s++) grow1();
            } else {
                random_init(h_);
            }
            cost = evalcost();
            bestc = cost;
            stall = 0;
        }
    }

    if (bh == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bh, bh * d_);
    for (int a = 0; a < bh; a++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", a, bh + bperm[l][a]);
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

    # The engine stops itself at `budget`; the subprocess timeout is a safety net.
    budget = max(0.5, time_limit - 3.0)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 2.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
