import time

import lib


# ---------------------------------------------------------------------------
# Engine A (new): bi-Cayley / Haar-type search.
# Graph: vertices A_g, B_g (g in G); A_g ~ B_{g*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so distances from A_0 and B_0 to
# all vertices determine the diameter exactly. Search over metacyclic groups
# Z_m x|_r Z_k with simulated annealing on the d-element connection set.
# ---------------------------------------------------------------------------
C_HAAR = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define GMAX 1200
#define DMAX 16
#define CANDMAX 8192

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
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

static int d_, D_, G_;
static int *MUL = NULL, *INV = NULL;
static int *NB = NULL;           /* NB[v*d+t]: t-th neighbour of v; v<G is A_v, v>=G is B_{v-G} */
static int S[DMAX];
static int *dist_ = NULL, *q_ = NULL;
static int candM[CANDMAX], candK[CANDMAX], candR[CANDMAX];
static int *bestE = NULL;
static int bestG = 0;

/* Group Z_m x|_r Z_k, element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int build_group(int m, int k, int r) {
    int G = m * k;
    if (G < 1 || G > GMAX) return 0;
    int *pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = (int)(1 % m);
    for (int t = 1; t < k; t++) pw[t] = (int)((long long)pw[t - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int aa = (int)((a + (long long)pw[b] * c) % m);
            MUL[x * G + y] = aa * k + (b + e) % k;
        }
    }
    free(pw);
    G_ = G;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (MUL[x * G + y] == 0) { INV[x] = y; break; }
    return 1;
}

static void set_col(int t, int s) {
    int G = G_, d = d_;
    S[t] = s;
    for (int g = 0; g < G; g++) {
        NB[g * d + t] = G + MUL[g * G + s];
        NB[(G + g) * d + t] = MUL[g * G + INV[s]];
    }
}

static int reach_from(int src) {
    int N = 2 * G_, d = d_;
    for (int v = 0; v < N; v++) dist_[v] = -1;
    int h = 0, tl = 0;
    q_[tl++] = src;
    dist_[src] = 0;
    while (h < tl) {
        int v = q_[h++];
        if (dist_[v] >= D_) continue;
        for (int t = 0; t < d; t++) {
            int w = NB[v * d + t];
            if (dist_[w] < 0) { dist_[w] = dist_[v] + 1; q_[tl++] = w; }
        }
    }
    return tl;
}

/* Unreached pairs from A_0 and from B_0. Zero iff diameter <= D. */
static long long cost_fn(void) {
    int N = 2 * G_;
    return (long long)(N - reach_from(0)) + (long long)(N - reach_from(G_));
}

static int in_set_upto(int x, int n) {
    for (int t = 0; t < n; t++) if (S[t] == x) return 1;
    return 0;
}

static int search_run(double tend) {
    int d = d_, G = G_;
    const long long stall_lim = 40000;
    for (int t = 0; t < d; t++) {
        int x;
        do { x = rndi(G); } while (in_set_upto(x, t));
        set_col(t, x);
    }
    long long cost = cost_fn();
    long long best = cost;
    double T0 = 0.05 * (double)(cost > 0 ? cost : 1);
    if (T0 < 1.0) T0 = 1.0;
    double t0 = now();
    double span = tend - t0;
    if (span < 1e-3) span = 1e-3;
    double temp = T0;
    long long last = 0;
    for (long long it = 0; cost > 0; it++) {
        if ((it & 127) == 0) {
            double tn = now();
            if (tn > tend) break;
            double frac = (tn - t0) / span;
            temp = T0 * (1.0 - frac) + 0.3;
        }
        if (it - last > stall_lim) {
            for (int t2 = 0; t2 < d; t2++) {
                int x2;
                do { x2 = rndi(G); } while (in_set_upto(x2, t2));
                set_col(t2, x2);
            }
            cost = cost_fn();
            best = cost;
            last = it;
            continue;
        }
        int t = rndi(d);
        int x = rndi(G);
        if (in_set_upto(x, d)) continue;
        int old = S[t];
        set_col(t, x);
        long long c2 = cost_fn();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < best) { best = cost; last = it; }
        } else {
            set_col(t, old);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long long minN = argc > 5 ? atoll(argv[5]) : 2;
    if (d_ < 3 || d_ > DMAX || D_ < 3) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    MUL = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    INV = malloc(sizeof(int) * GMAX);
    NB = malloc(sizeof(int) * (size_t)2 * GMAX * DMAX);
    dist_ = malloc(sizeof(int) * 2 * GMAX);
    q_ = malloc(sizeof(int) * 2 * GMAX);
    bestE = malloc(sizeof(int) * (size_t)2 * GMAX * DMAX);

    double tend = now() + tl;
    double slice = tl / 10.0;
    if (slice < 0.5) slice = 0.5;
    long long Gmin = minN / 2 + 1;   /* Haar order 2G must exceed minN */
    if (Gmin < d_ + 1) Gmin = d_ + 1;

    while (now() < tend) {
        int G = (int)Gmin + rndi(12);
        if (G > GMAX) break;
        int nc = 0;
        for (int m = 1; m <= G; m++) {
            if (G % m) continue;
            int k = G / m;
            for (int r = 0; r < m; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod(r, k, m) != (1 % m)) continue;
                if (nc < CANDMAX) { candM[nc] = m; candK[nc] = k; candR[nc] = r; nc++; }
            }
        }
        if (nc == 0) continue;
        int c = rndi(nc);
        if (!build_group(candM[c], candK[c], candR[c])) continue;
        double gend = now() + slice;
        if (gend > tend) gend = tend;
        if (search_run(gend)) {
            int d = d_;
            for (int g = 0; g < G; g++)
                for (int t = 0; t < d; t++) {
                    int p = g * d + t;
                    bestE[2 * p] = g;
                    bestE[2 * p + 1] = G + MUL[g * G + S[t]];
                }
            bestG = G;
            Gmin = G + 1;
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    int n = 2 * bestG, m = bestG * d_;
    printf("%d %d\n", n, m);
    for (int p = 0; p < m; p++) printf("%d %d\n", bestE[2 * p], bestE[2 * p + 1]);
    return 0;
}
'''


# ---------------------------------------------------------------------------
# Engine B (previous parent search, unchanged): voltage lifts over
# semidirect groups with simulated annealing and iterated local search.
# ---------------------------------------------------------------------------
C_PARENT = r'''
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
static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int *bE = NULL;
static int bEc = 0, bestN = 0;

/* Group Z_m x| Z_k2 with (a,b)(c,e) = (a + r^b c, b + e). Element a*k2+b. */
static int build_group(int m, int k2, int r) {
    int G = m * k2;
    if (G > GMAX) return 0;
    G_ = G;
    free(MT); free(RS);
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
    for (int g = 0; g < G; g++)
        for (int s = 0; s < G; s++)
            RS[s * G + MT[g * G + s]] = g;
    free(pwr);
    return 1;
}

static void alloc_state(int N) {
    free(nb); free(rch); free(tmpr);
    nb = malloc(sizeof(int) * (size_t)d_ * N);
    rch = malloc(sizeof(u64) * (size_t)N);
    tmpr = malloc(sizeof(u64) * (size_t)N);
    N_ = N;
}

/* Dart (l, i, j, s): A_{i,g} ~ B_{j, g*s}. */
static void setdart(int l, int i, int j, int s) {
    int G = G_, k = K_, N = N_;
    int *row = nb + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + j) * G + MT[g * G + s];
        row[(k + j) * G + g] = i * G + RS[s * G + g];
    }
}

static void apply_dart(int l, int i) { setdart(l, i, lay[l][i], VS[l][i]); }

static void snapshot(void) {
    memcpy(BL, lay, sizeof lay);
    memcpy(BV, VS, sizeof VS);
}

static void restore_snapshot(void) {
    int d = d_, k = K_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) { lay[l][i] = BL[l][i]; VS[l][i] = BV[l][i]; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) apply_dart(l, i);
}

/* Cost = unreached (representative, vertex) pairs + heavy penalty for duplicate darts. */
static long long evalcost(void) {
    int N = N_, G = G_, k = K_, d = d_;
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
    return unreached + 1000 * dup;
}

/* Simulated annealing with iterated-local-search kicks from the best state.
   Returns 1 when a valid graph (cost 0) is in the current state. */
static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_, N = N_;
    u64 full = (1ULL << (2 * k)) - 1;
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
    long long cost = evalcost();
    double c0 = (double)(cost > 0 ? cost : 1);
    long long bestc = cost;
    snapshot();
    int last = 0, kicks = 0;

    for (int t = 0; t < iters && cost != 0; t++) {
        if ((t & 63) == 0 && now() > tend) break;
        if (t - last > patience) {
            if (kicks >= maxkick) break;
            kicks++;
            restore_snapshot();
            for (int q = 0; q < 3; q++) {
                int l = rndi(d), i = rndi(k);
                VS[l][i] = rndi(G);
                apply_dart(l, i);
            }
            cost = evalcost();
            if (cost < bestc) { bestc = cost; snapshot(); }
            last = t;
            continue;
        }
        double temp = 0.02 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.3) temp = 0.3;

        if (k >= 2 && rndu() < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
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
            /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
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
        if (cost < bestc) { bestc = cost; last = t; snapshot(); }
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
    if (minN < 2) minN = 2;
    if (d_ < 3 || D_ < 3 || d_ > MAXD) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double tend = now() + tl;
    /* Per-group time slice: keeps one unlucky group from eating the budget. */
    double slice = tl / 6.0;
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
        int ok = search(gend, 20000, 3000, 6);
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
    start = time.monotonic()
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

    total = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    t_new = 0.45 * total

    # Engine A: bi-Cayley (Haar-type) search over metacyclic groups.
    try:
        out = lib.run_c(C_HAAR, [d, D, seed, round(t_new, 2), best_n + 1],
                        timeout=t_new + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Engine B: lift search with the remaining time (keeps the proven route alive).
    remaining = max(0.5, time_limit - 10.0 - (time.monotonic() - start))
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_PARENT, [d, D, seed, round(remaining, 2), best_n + 1],
                            timeout=remaining + 3.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
