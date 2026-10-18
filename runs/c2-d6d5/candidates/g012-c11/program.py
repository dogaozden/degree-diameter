import time

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
#define AUG_ITERS 2500
#define AUG_EXTRA 400

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

/* ---------------- voltage-lift search (group Z_m x| Z_k2) ---------------- */

static int d_, D_, K_, G_, N_;
static int *MT = NULL, *RS = NULL;
static int *nb = NULL;
static u64 *rch = NULL, *tmpr = NULL;
static int lay[MAXD][MAXK], VS[MAXD][MAXK];
static int BL[MAXD][MAXK], BV[MAXD][MAXK];
static int bestN = 0, bestKG = 0;
static int *bE = NULL;
static int bEc = 0;

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

static int search(double tend, int iters, int patience, int maxkick) {
    int k = K_, d = d_, G = G_;
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
            int l = 0, i = 0, picked = 0;
            if (rndu() < 0.4) {
                int start = rndi(N_), v = -1;
                for (int q = 0; q < N_; q++) {
                    int w = (start + q) % N_;
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

/* ---------------- NEW: double-edge-swap augmentation ----------------
   Given a d-regular bipartite graph of diameter <= D, add two vertices x (side A)
   and y (side B): remove a matching a_i-b_i (i < d), join x to all b_i and y to all a_i.
   Degrees are still exactly d. Then anneal with degree-preserving double-edge swaps
   (a1-b1, a2-b2 -> a1-b2, a2-b1), minimising the ordered count of pairs at distance > D.
   A zero-cost state is a valid graph with 2 more vertices. */

static int *adj = NULL;          /* adj[v*d + s] */
static int *LA = NULL;           /* list of A-side vertices */
static int nA_ = 0, cur_n = 0;
static int *sv_nb = NULL, *sv_LA = NULL;
static int sv_n = 0, sv_nA = 0;
static u64 *RC = NULL, *RN = NULL;
static int aug_cap = 0;

typedef struct { int a1, s1, a2, s2, b1, b2, t1, t2; } Sw;

static int adj_has(int v, int u) {
    int d = d_;
    for (int s = 0; s < d; s++) if (adj[v * d + s] == u) return 1;
    return 0;
}

static int adj_slot(int v, int u) {
    int d = d_;
    for (int s = 0; s < d; s++) if (adj[v * d + s] == u) return s;
    return -1;
}

static long long eval_bad(void) {
    int n = cur_n, d = d_, W = (n + 63) / 64;
    u64 *C = RC, *X = RN;
    memset(C, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++) C[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D_; t++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = X + (size_t)v * W;
            const u64 *src = C + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int s = 0; s < d; s++) {
                const u64 *q = C + (size_t)adj[v * d + s] * W;
                for (int w = 0; w < W; w++) dst[w] |= q[w];
            }
        }
        u64 *sw = C; C = X; X = sw;
    }
    long long cnt = 0;
    for (size_t i = 0; i < (size_t)n * W; i++) cnt += popc(C[i]);
    return (long long)n * n - cnt;
}

static int do_swap(int a1, int s1, int a2, int s2, Sw *u) {
    int d = d_;
    int b1 = adj[a1 * d + s1], b2 = adj[a2 * d + s2];
    if (a1 == a2 || b1 == b2) return 0;
    if (adj_has(a1, b2) || adj_has(a2, b1)) return 0;
    int t1 = adj_slot(b1, a1), t2 = adj_slot(b2, a2);
    adj[a1 * d + s1] = b2; adj[a2 * d + s2] = b1;
    adj[b1 * d + t1] = a2; adj[b2 * d + t2] = a1;
    u->a1 = a1; u->s1 = s1; u->a2 = a2; u->s2 = s2;
    u->b1 = b1; u->b2 = b2; u->t1 = t1; u->t2 = t2;
    return 1;
}

static void undo_swap(const Sw *u) {
    int d = d_;
    adj[u->a1 * d + u->s1] = u->b1; adj[u->a2 * d + u->s2] = u->b2;
    adj[u->b1 * d + u->t1] = u->a1; adj[u->b2 * d + u->t2] = u->a2;
}

static int add_pair(void) {
    int d = d_;
    int ma[MAXD], mb[MAXD], m = 0;
    for (int tr = 0; tr < 4000 && m < d; tr++) {
        int a = LA[rndi(nA_)], s = rndi(d);
        int b = adj[a * d + s];
        int ok = 1;
        for (int i = 0; i < m; i++) if (ma[i] == a || mb[i] == b) { ok = 0; break; }
        if (ok) { ma[m] = a; mb[m] = b; m++; }
    }
    if (m < d) return 0;
    int x = cur_n, y = cur_n + 1;
    cur_n += 2;
    for (int i = 0; i < d; i++) {
        int ta = adj_slot(ma[i], mb[i]);
        int tb = adj_slot(mb[i], ma[i]);
        adj[ma[i] * d + ta] = y;
        adj[mb[i] * d + tb] = x;
        adj[x * d + i] = mb[i];
        adj[y * d + i] = ma[i];
    }
    LA[nA_++] = x;
    return 1;
}

static int anneal(int iters, double tend) {
    int d = d_;
    long long cost = eval_bad();
    if (cost == 0) return 1;
    double T0 = 0.02 * (double)cost;
    if (T0 < 2.0) T0 = 2.0;
    double T1 = 0.3;
    for (int it = 0; it < iters; it++) {
        if ((it & 15) == 0 && now() > tend) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a1 = LA[rndi(nA_)], a2 = LA[rndi(nA_)];
        int s1 = rndi(d), s2 = rndi(d);
        Sw u;
        if (!do_swap(a1, s1, a2, s2, &u)) continue;
        long long c2 = eval_bad();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
            if (cost == 0) return 1;
        } else {
            undo_swap(&u);
        }
    }
    return 0;
}

static void aug_save(void) {
    memcpy(sv_nb, adj, sizeof(int) * (size_t)cur_n * d_);
    memcpy(sv_LA, LA, sizeof(int) * (size_t)nA_);
    sv_n = cur_n; sv_nA = nA_;
}

static void aug_load(void) {
    memcpy(adj, sv_nb, sizeof(int) * (size_t)sv_n * d_);
    memcpy(LA, sv_LA, sizeof(int) * (size_t)sv_nA);
    cur_n = sv_n; nA_ = sv_nA;
}

static int aug_run(double tend, int maxadd) {
    int added = 0;
    while (now() < tend && added < maxadd) {
        if (cur_n + 2 > aug_cap) break;
        aug_load();
        if (!add_pair()) continue;
        if (anneal(AUG_ITERS, tend)) {
            aug_save();
            added++;
        }
    }
    return added;
}

static int init_aug(int n, int kG, const int *E, int m) {
    int d = d_;
    int *deg = calloc((size_t)n, sizeof(int));
    if (!deg) return 0;
    for (int p = 0; p < m; p++) {
        int u = E[2 * p], v = E[2 * p + 1];
        if (u < 0 || v < 0 || u >= n || v >= n || deg[u] >= d || deg[v] >= d) {
            free(deg);
            return 0;
        }
        adj[u * d + deg[u]++] = v;
        adj[v * d + deg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        if (deg[v] != d) { free(deg); return 0; }
    free(deg);
    cur_n = n; nA_ = kG;
    for (int i = 0; i < kG; i++) LA[i] = i;
    return 1;
}

static void emit_saved(void) {
    int d = d_;
    printf("%d %d\n", sv_n, sv_nA * d);
    for (int i = 0; i < sv_nA; i++) {
        int a = sv_LA[i];
        for (int s = 0; s < d; s++) printf("%d %d\n", a, sv_nb[a * d + s]);
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
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double tend = t0 + tl - 0.5;
    double lift_end = t0 + 0.6 * tl;
    double slice = (lift_end - t0) / 6.0;
    if (slice < 1.0) slice = 1.0;
    static const int Ks[10] = {1, 1, 1, 2, 2, 2, 3, 3, 4, 5};
    static const int K2s[13] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12};
    static int cand[GMAX + 5];

    while (now() < lift_end) {
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
        if (gend > lift_end) gend = lift_end;
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
            bestKG = kG;
            minN = N_ + 1;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }

    /* Augmentation stage on the best lift. */
    int d = d_;
    aug_cap = bestN + AUG_EXTRA;
    int Wc = (aug_cap + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)aug_cap * d);
    LA = malloc(sizeof(int) * (size_t)aug_cap);
    sv_nb = malloc(sizeof(int) * (size_t)aug_cap * d);
    sv_LA = malloc(sizeof(int) * (size_t)aug_cap);
    RC = malloc(sizeof(u64) * (size_t)aug_cap * Wc);
    RN = malloc(sizeof(u64) * (size_t)aug_cap * Wc);

    if (!init_aug(bestN, bestKG, bE, bEc)) {
        printf("%d %d\n", bestN, bEc);
        for (int p = 0; p < bEc; p++) printf("%d %d\n", bE[2 * p], bE[2 * p + 1]);
        return 0;
    }
    aug_save();
    aug_run(tend, AUG_EXTRA / 2);
    emit_saved();
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

    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best_n + 1],
                        timeout=budget + 6.0)
        n, e = lib.parse_graph_text(out)
        if n > 0:
            consider(n, e)
    except Exception:
        pass

    _ = time.monotonic() - start
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
