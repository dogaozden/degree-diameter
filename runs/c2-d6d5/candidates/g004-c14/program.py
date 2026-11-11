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
        int ok = search(tend, 20000, 3000, 6);
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


# Growth engine: takes a d-regular bipartite graph (A = first half of the
# labels, B = second half) and repeatedly adds one A and one B vertex by a
# degree-preserving splice, then anneals with double-edge swaps until the
# diameter is at most D again. Each successful growth becomes the new base.
C_GROW = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define MAXN 2048
#define MAXD 16
#define MAXW 32

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

static int d_, D_, N_, Wn_;
static int nb_[MAXN * MAXD];
static int side_[MAXN];
static int Alist[MAXN], Blist[MAXN], nA_, nB_;
static u64 bufA_[MAXN * MAXW], bufB_[MAXN * MAXW];
static int base_nb_[MAXN * MAXD];
static int base_side_[MAXN];
static int base_N_;
static int stampA_[MAXN], stampB_[MAXN], stamp_ = 0;

static int findslot(int v, int u) {
    int d = d_;
    for (int l = 0; l < d; l++) if (nb_[v * d + l] == u) return l;
    return -1;
}
static int isadj(int a, int b) { return findslot(a, b) >= 0; }

static void rebuild_lists(void) {
    nA_ = nB_ = 0;
    for (int v = 0; v < N_; v++) {
        if (side_[v] == 0) Alist[nA_++] = v;
        else Blist[nB_++] = v;
    }
}

/* Number of ordered pairs (u, v) with dist(u, v) > D_. Zero iff valid. */
static long long evalbad(void) {
    int N = N_, d = d_, Wn = Wn_;
    u64 *c = bufA_, *x = bufB_;
    memset(c, 0, sizeof(u64) * (size_t)N * Wn);
    for (int v = 0; v < N; v++) c[(size_t)v * Wn + (size_t)(v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < N; v++) {
            u64 *o = x + (size_t)v * Wn;
            const u64 *s = c + (size_t)v * Wn;
            for (int w = 0; w < Wn; w++) o[w] = s[w];
            for (int l = 0; l < d; l++) {
                const u64 *q = c + (size_t)nb_[v * d + l] * Wn;
                for (int w = 0; w < Wn; w++) o[w] |= q[w];
            }
        }
        u64 *tmp = c; c = x; x = tmp;
    }
    long long cnt = 0;
    size_t tot = (size_t)N * Wn;
    for (size_t i = 0; i < tot; i++) cnt += popc(c[i]);
    return (long long)N * N - cnt;
}

/* Degree-preserving splice: pick a matching of d edges (a_i, b_i), replace each
   by (a_i, y) and (x, b_i) for new vertices x (side A) and y (side B). */
static int grow_once(void) {
    int d = d_, N = N_;
    if (N + 2 > MAXN || nA_ < 1) return 0;
    int x = N, y = N + 1;
    int ca[MAXD], cb[MAXD];
    int k = 0;
    stamp_++;
    long tries = 0;
    while (k < d && tries < 200000) {
        tries++;
        int a = Alist[rndi(nA_)];
        int b = nb_[a * d + rndi(d)];
        if (stampA_[a] == stamp_ || stampB_[b] == stamp_) continue;
        stampA_[a] = stamp_; stampB_[b] = stamp_;
        ca[k] = a; cb[k] = b; k++;
    }
    if (k < d) return 0;
    for (int i = 0; i < d; i++) {
        int a = ca[i], b = cb[i];
        int sa = findslot(a, b), sb = findslot(b, a);
        nb_[a * d + sa] = y;
        nb_[b * d + sb] = x;
        nb_[y * d + i] = a;
        nb_[x * d + i] = b;
    }
    side_[x] = 0; side_[y] = 1;
    N_ = N + 2;
    Wn_ = (N_ + 63) / 64;
    rebuild_lists();
    return 1;
}

/* Annealing with double-edge swaps (degree and bipartition preserved).
   Returns 1 as soon as the cost is 0. */
static int anneal(double dur, double T0) {
    int d = d_;
    double t0 = now(), tend = t0 + dur;
    long long cost = evalbad();
    if (cost == 0) return 1;
    double T = T0;
    long long it = 0;
    while (1) {
        if ((it & 31) == 0) {
            double t = now();
            if (t > tend) break;
            double frac = (t - t0) / dur;
            if (frac > 1.0) frac = 1.0;
            T = T0 * (1.0 - frac) + 0.5;
        }
        it++;
        int a1 = Alist[rndi(nA_)], a2 = Alist[rndi(nA_)];
        if (a1 == a2) continue;
        int l1 = rndi(d), l2 = rndi(d);
        int b1 = nb_[a1 * d + l1], b2 = nb_[a2 * d + l2];
        if (b1 == b2) continue;
        if (isadj(a1, b2) || isadj(a2, b1)) continue;
        int s1 = findslot(b1, a1), s2 = findslot(b2, a2);
        nb_[a1 * d + l1] = b2; nb_[a2 * d + l2] = b1;
        nb_[b1 * d + s1] = a2; nb_[b2 * d + s2] = a1;
        long long c2 = evalbad();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            nb_[a1 * d + l1] = b1; nb_[a2 * d + l2] = b2;
            nb_[b1 * d + s1] = a1; nb_[b2 * d + s2] = a2;
        }
    }
    return 0;
}

static void save_base(void) {
    base_N_ = N_;
    memcpy(base_nb_, nb_, sizeof(int) * (size_t)N_ * d_);
    memcpy(base_side_, side_, sizeof(int) * (size_t)N_);
}

static void restore_base(void) {
    N_ = base_N_;
    memcpy(nb_, base_nb_, sizeof(int) * (size_t)N_ * d_);
    memcpy(side_, base_side_, sizeof(int) * (size_t)N_);
    Wn_ = (N_ + 63) / 64;
    rebuild_lists();
}

/* Reads "n m" and m edges; returns 1 if the graph is bipartite (A = first half),
   simple and d-regular. */
static int read_graph(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n < 4 || n > MAXN || (n & 1) || m < 0) return 0;
    int M = n / 2;
    int d = d_;
    static int deg[MAXN];
    for (int v = 0; v < n; v++) { deg[v] = 0; side_[v] = (v >= M); }
    N_ = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || u >= n || v < 0 || v >= n) return 0;
        if ((u < M) == (v < M)) return 0;
        if (deg[u] >= d || deg[v] >= d) return 0;
        for (int l = 0; l < deg[u]; l++) if (nb_[u * d + l] == v) return 0;
        nb_[u * d + deg[u]++] = v;
        nb_[v * d + deg[v]++] = u;
    }
    for (int v = 0; v < n; v++) if (deg[v] != d) return 0;
    Wn_ = (N_ + 63) / 64;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d_ < 2 || d_ > MAXD || D_ < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tend = now() + tl;

    if (!read_graph()) { printf("0 0\n"); return 0; }
    rebuild_lists();

    int base_valid = 0;
    {
        double rem = tend - now();
        if (evalbad() == 0) base_valid = 1;
        else if (rem > 1.0 && anneal(rem * 0.2, 6.0)) base_valid = 1;
    }
    save_base();

    int fails = 0;
    while (1) {
        double rem = tend - now();
        if (rem < 1.0) break;
        if (N_ + 2 > MAXN || fails > 50) break;
        restore_base();
        if (!grow_once()) { fails++; continue; }
        double dur = rem * 0.4;
        if (dur < 1.0) dur = rem - 0.5;
        if (anneal(dur, 6.0)) {
            save_base();
            base_valid = 1;
        }
    }

    if (!base_valid) { printf("0 0\n"); return 0; }
    int N = base_N_, d = d_;
    printf("%d %d\n", N, N * d / 2);
    for (int v = 0; v < N; v++) {
        if (base_side_[v] != 0) continue;
        for (int l = 0; l < d; l++) printf("%d %d\n", v, base_nb_[v * d + l]);
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

    # Total search time, leaving slack for compile, parsing and validation.
    t_total = max(0.0, time_limit - 8.0)
    if t_total < 2.0:
        return best

    # Stage 1: group-lift search (the proven engine) for a strong base graph.
    b1 = round(0.45 * t_total, 2)
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, b1, best_n + 1], timeout=b1 + 3.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    # Stage 2: grow the best valid graph by degree-preserving splices and repair
    # with double-edge-swap annealing. Starts from whatever stage 1 produced.
    b2 = round(t_total - b1, 2)
    if b2 >= 1.0 and best_n > 0:
        try:
            out2 = lib.run_c(C_GROW, [d, D, seed + 7, b2], stdin_graph=best,
                             timeout=b2 + 3.0)
            n2, e2 = lib.parse_graph_text(out2)
            if n2 > 0:
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
