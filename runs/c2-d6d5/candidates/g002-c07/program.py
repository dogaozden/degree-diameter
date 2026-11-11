"""Harder search for d=6, D=5 (and other targets), with a different search engine.

Changes from the parent:
- C engine: tabu steepest-descent over sampled moves replaces simulated annealing.
  Each step evaluates NCAND random moves (voltage change or layout swap), takes the
  best non-tabu one, and restarts after a stagnation limit.
- Wider base graphs (up to 6 vertices per side) and more group shapes, with group
  orders steered to just above the current best order (a ratchet).
- Python: PG(2,q) and Araujo-Lopez fallbacks, both checked with lib.is_valid,
  with K_{d,d} as the last resort.
"""
import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

typedef uint64_t u64;

#define MAXD 16
#define MAXK 16
#define GMAX 1600
#define NCAND 16

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (u64)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m; b %= m;
    while (e > 0) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, k_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static long long tabu_until[MAXD][MAXK];
static int *bestE = NULL;
static int bestEc = 0, bestN = 0;
static int cand[GMAX + 1];

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element (a,b) = a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    free(MT); free(RS);
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            long long aa = ((long long)a + (long long)pwr[b] * c) % m;
            MT[x * G + y] = (int)(aa * k2 + (b + e) % k2);
        }
    }
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * N);
    tmpr = malloc(sizeof(u64) * N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. Vertex index: A_i -> i*G+g, B_j -> (k+j)*G+g. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = k_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void set_volt(int l, int i, int s) {
    VS[l][i] = s;
    setdart(l, i, lay[l][i], s);
}

static void swap_lay(int l, int i1, int i2) {
    int t = lay[l][i1]; lay[l][i1] = lay[l][i2]; lay[l][i2] = t;
    setdart(l, i1, lay[l][i1], VS[l][i1]);
    setdart(l, i2, lay[l][i2], VS[l][i2]);
}

/* Lift is G-invariant, so checking reach from every vertex to each fibre identity is exact. */
static long long evalcost(void) {
    int N = N_, G = G_, k = k_, d = d_;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < 2 * k; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long cnt = 0;
    for (int v = 0; v < N; v++) cnt += popc(rch[v]);
    long long unreached = (long long)2 * k * N - cnt;
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    return unreached + 1000LL * dup;
}

/* Tabu steepest descent over sampled moves. Returns 1 if a cost-0 lift is found. */
static int run_search(double tend, int maxstag) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) { lay[l][i] = perm[i]; VS[l][i] = rndi(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            setdart(l, i, lay[l][i], VS[l][i]);
    memset(tabu_until, 0, sizeof tabu_until);

    long long cost = evalcost();
    long long bc = cost;
    int stag = 0;
    for (long long it = 1; ; it++) {
        if (cost == 0) return 1;
        if (stag > maxstag) return 0;
        if ((it & 15) == 0 && now_s() > tend) return 0;

        long long bcand = LLONG_MAX;
        int mt = -1, ml = 0, mi = 0, mi2 = 0, mv = 0;
        for (int c = 0; c < NCAND; c++) {
            if (k >= 2 && rndu() < 0.3) {
                int l = rndi(d), i1 = rndi(k), i2 = rndi(k - 1);
                if (i2 >= i1) i2++;
                swap_lay(l, i1, i2);
                long long c2 = evalcost();
                swap_lay(l, i1, i2);
                int tb = (tabu_until[l][i1] > it) || (tabu_until[l][i2] > it);
                if (tb && c2 >= bc) continue;
                if (c2 < bcand || (c2 == bcand && rndi(2))) {
                    bcand = c2; mt = 1; ml = l; mi = i1; mi2 = i2;
                }
            } else {
                int l = rndi(d), i = rndi(k), nw = rndi(G);
                if (nw == VS[l][i]) continue;
                int old = VS[l][i];
                set_volt(l, i, nw);
                long long c2 = evalcost();
                set_volt(l, i, old);
                if (tabu_until[l][i] > it && c2 >= bc) continue;
                if (c2 < bcand || (c2 == bcand && rndi(2))) {
                    bcand = c2; mt = 0; ml = l; mi = i; mv = nw;
                }
            }
        }
        if (mt < 0) continue;
        long long ten = it + 3 + rndi(6);
        if (mt == 1) {
            swap_lay(ml, mi, mi2);
            tabu_until[ml][mi] = ten;
            tabu_until[ml][mi2] = ten;
        } else {
            set_volt(ml, mi, mv);
            tabu_until[ml][mi] = ten;
        }
        cost = bcand;
        if (cost < bc) { bc = cost; stag = 0; } else stag++;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int minN = atoi(argv[5]);
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    double tend = now_s() + tl;
    static const int Ks[12] = {1, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5, 6};
    static const int K2s[16] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 16};

    while (now_s() < tend) {
        int k = Ks[rndi(12)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 40 + 2);
        int k2 = K2s[rndi(16)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        k_ = k;
        G_ = m * k2;
        alloc_state(2 * k_ * G_);
        if (run_search(tend, 1200)) {
            int N = N_;
            if (N > bestN) {
                int kG = k_ * G_;
                int cnt = kG * d_;
                int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
                int p = 0;
                for (int u = 0; u < kG; u++)
                    for (int l = 0; l < d_; l++) {
                        ne[2 * p] = u;
                        ne[2 * p + 1] = nb[l * N + u];
                        p++;
                    }
                free(bestE);
                bestE = ne;
                bestEc = cnt;
                bestN = N;
                minN = N + 1 + rndi(N / 100 + 1);
            }
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestEc);
    for (int p = 0; p < bestEc; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
        for make in (_best_pg, _araujo):
            try:
                g = make(d)
            except Exception:
                g = None
            if g is not None:
                consider(g[0], g[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best  # exact optimum

    if d < 3 or D < 3:
        return best

    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
