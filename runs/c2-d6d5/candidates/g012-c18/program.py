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
#define MAXK 8
#define GMAX 2000

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

/* Globals: group-lift state.
   Vertices: A-block i (0..k-1) and B-block j (k..2k-1), each block = G group elements.
   Vertex index = block*G + group element. Layer l gives a permutation lay[l][.] of
   the A->B block matching, with voltage VS[l][i]: A_{i,g} ~ B_{j,g*s}. */
static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static long long *Wt = NULL;      /* breakout weights for (rep block b, vertex v) */
static long long DW = 2;          /* weight of a duplicate dart pair */
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b, identity 0. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    free(MT); free(RS);
    G_ = G;
    MT = malloc(sizeof(int) * (size_t)G * G);
    RS = malloc(sizeof(int) * (size_t)G * G);
    int *pwr = malloc(sizeof(int) * (size_t)k2);
    pwr[0] = 1 % m;
    for (int t = 1; t < k2; t++) pwr[t] = (int)((long long)pwr[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int aa = (int)((a + (long long)pwr[b] * c) % m);
            MT[x * G + y] = aa * k2 + (b + e) % k2;
        }
    }
    /* RS[s*G + x*s] = x : inverse of right multiplication by s. */
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr); free(Wt);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    Wt = malloc(sizeof(long long) * (size_t)(2 * K_) * N);
    N_ = N;
}

static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

/* Bitmask BFS from the 2k representatives (block b, identity element).
   By left-invariance of the lift this decides diameter exactly.
   wc = weighted unreached pairs + DW * duplicate darts; uc = unreached; dc = duplicates. */
static void evaluate(long long *wc, long long *uc, long long *dc) {
    int N = N_, G = G_, k = K_, d = d_;
    int nbk = 2 * k;
    for (int v = 0; v < N; v++) rch[v] = 0;
    for (int b = 0; b < nbk; b++) rch[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 x = rch[v];
            for (int l = 0; l < d; l++) x |= rch[nb[(size_t)l * N + v]];
            tmpr[v] = x;
        }
        u64 *sw = rch; rch = tmpr; tmpr = sw;
    }
    long long W = 0, U = 0;
    for (int b = 0; b < nbk; b++) {
        long long *wb = Wt + (size_t)b * N;
        for (int v = 0; v < N; v++)
            if (!((rch[v] >> b) & 1ULL)) { U++; W += wb[v]; }
    }
    long long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (lay[l][i] == lay[l2][i] && VS[l][i] == VS[l2][i]) dup++;
    *wc = W + DW * dup;
    *uc = U;
    *dc = dup;
}

/* Breakout: at a local minimum, raise the weight of every currently unreached
   (representative, vertex) pair and of duplicate darts, so the landscape changes. */
static void breakout(long long *cur, long long *U, long long *dup) {
    int N = N_, nbk = 2 * K_;
    long long wc, u, dp;
    evaluate(&wc, &u, &dp);
    for (int b = 0; b < nbk; b++)
        for (int v = 0; v < N; v++)
            if (!((rch[v] >> b) & 1ULL)) Wt[(size_t)b * N + v]++;
    if (dp > 0) DW++;
    evaluate(&wc, &u, &dp);
    *cur = wc; *U = u; *dup = dp;
}

/* Weighted breakout local search. Returns 1 when the current state is a valid lift. */
static int search(double tend, long long maxsteps) {
    int k = K_, d = d_, G = G_, N = N_, nbk = 2 * k;
    u64 full = (1ULL << nbk) - 1;
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
        for (int i = 0; i < k; i++) apply_dart(l, i);
    for (size_t q = 0; q < (size_t)nbk * N; q++) Wt[q] = 1;
    DW = 2;

    long long cur, U, dup;
    evaluate(&cur, &U, &dup);
    int stall = 0;
    const int PAT = 25;

    for (long long t = 0; t < maxsteps; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (U == 0 && dup == 0) return 1;
        long long before = cur;
        long long nc, nU, ndup;

        if (k >= 2 && rndu() < 0.2) {
            /* Layer swap: exchange B-targets of two A-blocks in one layer. */
            int l = rndi(d);
            int i1 = rndi(k), i2 = rndi(k - 1);
            if (i2 >= i1) i2++;
            int t1 = lay[l][i1], t2 = lay[l][i2];
            lay[l][i1] = t2; lay[l][i2] = t1;
            apply_dart(l, i1); apply_dart(l, i2);
            evaluate(&nc, &nU, &ndup);
            if (nc <= cur) { cur = nc; U = nU; dup = ndup; }
            else {
                lay[l][i1] = t1; lay[l][i2] = t2;
                apply_dart(l, i1); apply_dart(l, i2);
            }
        } else {
            /* Voltage change, targeted at an unsatisfied vertex half the time. */
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.5) {
                int start = rndi(N), v = -1;
                for (int q = 0; q < N; q++) {
                    int w = (start + q) % N;
                    if (rch[w] != full) { v = w; break; }
                }
                if (v >= 0) {
                    int b = v / G;
                    l = rndi(d);
                    if (b < k) i = b;
                    else {
                        int jb = b - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (lay[l][ii] == jb) { i = ii; break; }
                        if (i < 0) i = rndi(k);
                    }
                    picked = 1;
                }
            }
            if (!picked) { l = rndi(d); i = rndi(k); }
            int old = VS[l][i];
            int nw = (old + 1 + rndi(G - 1)) % G;   /* G >= 2, always a change */
            VS[l][i] = nw;
            apply_dart(l, i);
            evaluate(&nc, &nU, &ndup);
            if (nc <= cur) { cur = nc; U = nU; dup = ndup; }
            else {
                VS[l][i] = old;
                apply_dart(l, i);
            }
        }

        if (cur < before) stall = 0; else stall++;
        if (stall >= PAT) {
            breakout(&cur, &U, &dup);
            stall = 0;
        }
    }
    return (U == 0 && dup == 0);
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
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    double slice = tl / 5.0;
    if (slice < 1.0) slice = 1.0;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < tend) {
        int k = Ks[rndi(10)];
        if (k > MAXK) k = MAXK;
        int Gmin = (minN + 2 * k - 1) / (2 * k);
        if (Gmin < 2) Gmin = 2;
        Gmin += rndi(Gmin / 30 + 3);
        int k2 = K2s[rndi(13)];
        int m = (Gmin + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (int r = 1; r < m; r++)
            if (gcd_i(r, m) == 1 && powmod(r, k2, m) == 1 % m) cand[nc++] = r;
        if (nc == 0) continue;
        int r = cand[rndi(nc)];
        if (!build_group(m, k2, r)) continue;
        K_ = k;
        alloc_state(2 * k * G_);
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        int ok = search(gend, 100000000LL);
        if (ok && N_ > bestN) {
            int kG = K_ * G_;
            int cnt = kG * d_;
            int *ne = malloc(sizeof(int) * 2 * (size_t)cnt);
            int p = 0;
            for (int u = 0; u < kG; u++)
                for (int l = 0; l < d_; l++) {
                    ne[2 * p] = u;
                    ne[2 * p + 1] = nb[(size_t)l * N_ + u];
                    p++;
                }
            free(bE);
            bE = ne;
            bEc = cnt;
            bestN = N_;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bEc);
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

    budget = max(0.5, min(0.88 * time_limit, time_limit - 7.0))
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
