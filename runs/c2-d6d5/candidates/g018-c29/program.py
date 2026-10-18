import time

import lib


# ---------------------------------------------------------------------------
# Engine: voltage lifts over semidirect groups Z_m x| Z_k2 with k base blocks
# per side. Each lift is vertex-transitive within every block, so the diameter
# test needs BFS only from one representative per block (2k BFS runs) instead
# of all-pairs bitsets. Cost = unreached (representative, vertex) pairs at
# distance > D, plus a penalty for repeated darts. Cost 0 means diameter <= D.
# Simulated annealing over voltages and layer permutations, restarted over
# many random groups with growing order.
# ---------------------------------------------------------------------------
C_ENGINE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXD 12
#define MAXK 6
#define GMAX 800
#define NMAX (2 * MAXK * GMAX)
#define EMAX (MAXK * GMAX * MAXD + 16)

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
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int d_, D_, K_, G_;
static int PW[GMAX];
static int MT[GMAX * GMAX];
static int INV[GMAX];
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int nb[MAXD][NMAX];
static int dist_[NMAX], queue_[NMAX];
static int cand[GMAX + 5];
static int EA[EMAX], EB[EMAX];
static int bestN = 0, bestM = 0;

/* Group Z_m x| Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_group(int m, int k2, int r) {
    int G = m * k2;
    G_ = G;
    PW[0] = 1 % m;
    for (int t = 1; t < k2; t++) PW[t] = (int)((long long)PW[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)PW[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MT[x * G + y] == 0) { INV[x] = y; break; }
}

/* Dart (l, i, j = lay[l][i], s = VS[l][i]): A_{i,g} ~ B_{j, g*s}. */
static void apply_dart(int l, int i) {
    int G = G_, kG = K_ * G_;
    int j = lay[l][i], s = VS[l][i];
    int si = INV[s];
    for (int g = 0; g < G; g++)
        nb[l][i * G + g] = kG + j * G + MT[g * G + s];
    for (int h = 0; h < G; h++)
        nb[l][kG + j * G + h] = i * G + MT[h * G + si];
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) c++;
    return c;
}

static long long evalcost(void) {
    int k = K_, G = G_, d = d_, D = D_;
    int N = 2 * k * G;
    long long unreached = 0;
    for (int src = 0; src < 2 * k; src++) {
        int s0 = (src < k) ? src * G : k * G + (src - k) * G;
        for (int v = 0; v < N; v++) dist_[v] = -1;
        int qh = 0, qt = 0;
        dist_[s0] = 0;
        queue_[qt++] = s0;
        while (qh < qt) {
            int v = queue_[qh++];
            int dv = dist_[v];
            if (dv >= D) continue;
            for (int l = 0; l < d; l++) {
                int u = nb[l][v];
                if (dist_[u] < 0) {
                    dist_[u] = dv + 1;
                    queue_[qt++] = u;
                }
            }
        }
        unreached += N - qt;
    }
    return unreached + 1000LL * dupcount();
}

static void randomize(void) {
    int k = K_, G = G_, d = d_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            lay[l][i] = perm[i];
            VS[l][i] = rndi(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

static int search(double tend, long iters) {
    int k = K_, d = d_, G = G_;
    randomize();
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    for (long t = 0; t < iters && cost != 0; t++) {
        if ((t & 127) == 0 && now() > tend) break;
        double frac = (double)t / (double)iters;
        double temp = 0.03 * c0 * (1.0 - frac);
        if (temp < 0.3) temp = 0.3;
        if (k >= 2 && rndu() < 0.2) {
            /* Layer move: swap the targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1);
            apply_dart(l, i2);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1);
                apply_dart(l, i2);
            }
        } else {
            /* Voltage move. */
            int l = rndi(d), i = rndi(k);
            int old = VS[l][i];
            int nw = rndi(G);
            if (nw == old) continue;
            VS[l][i] = nw;
            apply_dart(l, i);
            long long c2 = evalcost();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (d_ < 3 || d_ > MAXD || D_ < 3) { printf("0 0\n"); return 0; }
    if (minN < 2) minN = 2;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    static const int Ks[10] = {1, 1, 1, 1, 2, 2, 2, 3, 4, 5};
    static const int K2s[10] = {1, 1, 2, 2, 3, 4, 6, 2, 3, 8};

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        int G0 = Gmin + rndi(Gmin / 40 + 3);
        int k2 = K2s[rndi(10)];
        int m = (G0 + k2 - 1) / k2;
        if (m < 2) m = 2;
        int G = m * k2;
        if (G > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        build_group(m, k2, r);
        K_ = k;
        int ok = search(tend, 40000);
        if (ok) {
            int kG = K_ * G_;
            int N = 2 * kG;
            if (N > bestN) {
                int p = 0;
                for (int u = 0; u < kG; u++)
                    for (int l = 0; l < d_; l++) {
                        EA[p] = u;
                        EB[p] = nb[l][u];
                        p++;
                    }
                bestN = N;
                bestM = p;
                minN = bestN + 1;
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int p = 0; p < bestM; p++) printf("%d %d\n", EA[p], EB[p]);
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
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid.
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

    # Time split: leave a margin for compilation, process start and parsing.
    total = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    engine_tl = max(0.5, total - 3.0)
    elapsed = time.monotonic() - start
    timeout = max(1.0, time_limit - elapsed - 1.5)

    try:
        out = lib.run_c(C_ENGINE, [d, D, seed, round(engine_tl, 2), best_n + 1],
                        timeout=timeout)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
