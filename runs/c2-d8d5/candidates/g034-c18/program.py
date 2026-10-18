"""Lift search for the d-regular bipartite diameter-D targets, with C growth afterwards.

New in this version: a C group-lift annealer (C_LIFT) that works over semidirect
products Z_m x| Z_k2 with k base vertices per side. Left translation by the group is an
automorphism of every such lift, so the number of bad ordered pairs is G times the sum of
unreached counts from only the 2k block representatives. Each evaluation is therefore about
2k BFS runs instead of N, which makes annealing over voltages and layer permutations
fast enough to climb to larger group orders. The group order is raised each time a lift
is found, so the search keeps going upward. The annealer from the previous version
(C_GROW) then uses any remaining time to add vertices to the best graph.
"""
import random
import time

import lib


# ----------------------------------------------------------------------------
# C group-lift annealer (new). Symmetry-reduced evaluation via block BFS sources.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

#define NMAX 20000
#define DMAX 16
#define KMAX 6
#define K2MAX 64

static int d_, D_, k_, k2_, m_, G_, N_, r_;
static int PW[K2MAX];
static int perm[DMAX][KMAX];
static int S[DMAX][KMAX];
static int adj[NMAX * DMAX];
static int fillc[NMAX];
static int distv[NMAX];
static int queuev[NMAX];
static int be_u[NMAX * DMAX / 2 + 1];
static int be_v[NMAX * DMAX / 2 + 1];
static int best_n = 0, best_m = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static int powmod_(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Semidirect product Z_m x| Z_k2, element a*k2+b: (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int na = (a + (int)((long long)PW[b] * c % m_)) % m_;
    int nb = (b + e) % k2_;
    return na * k2_ + nb;
}

/* Lift: vertex (i, x) for side-0 block i, (k+j, y) for side-1 block j; layer l joins
   (i, x) to (perm[l][i], x * S[l][i]). Each vertex then has degree exactly d_. */
static void build_adj(void) {
    int N = N_, d = d_, k = k_, G = G_;
    for (int v = 0; v < N; v++) fillc[v] = 0;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = perm[l][i], s = S[l][i];
            for (int x = 0; x < G; x++) {
                int u = i * G + x;
                int w = (k + j) * G + gmul(x, s);
                adj[u * d + fillc[u]++] = w;
                adj[w * d + fillc[w]++] = u;
            }
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (perm[l][i] == perm[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Bad ordered pairs, using left-translation symmetry: only the identity of each block
   is a BFS source. Zero iff the lift has diameter <= D_. */
static long long eval_cost(void) {
    int N = N_, D = D_, d = d_;
    long long total = 0;
    for (int b = 0; b < 2 * k_; b++) {
        int src = b * G_;
        for (int v = 0; v < N; v++) distv[v] = -1;
        int h = 0, t = 0;
        distv[src] = 0;
        queuev[t++] = src;
        while (h < t) {
            int v = queuev[h++];
            if (distv[v] >= D) continue;
            const int *nb = adj + (size_t)v * d;
            for (int q = 0; q < d; q++) {
                int u = nb[q];
                if (distv[u] < 0) { distv[u] = distv[v] + 1; queuev[t++] = u; }
            }
        }
        total += (long long)(N - t);
    }
    return total;
}

static long long full_cost(void) {
    build_adj();
    return eval_cost() + 1000LL * (long long)dupcount();
}

static int run_sa(double until) {
    double start = now_s();
    double span = until - start;
    if (span < 1e-3) span = 1e-3;
    long long cost = full_cost();
    double T0 = 5.0 + 0.05 * (double)cost, T1 = 0.5;
    while (cost > 0) {
        double el = now_s();
        if (el >= until) break;
        double T = T0 * pow(T1 / T0, (el - start) / span);
        int l = rint_(d_), i = rint_(k_);
        int kind;
        int oldS = S[l][i], i2 = -1;
        if (k_ < 2 || rint_(10) < 6) {
            int ns = rint_(G_);
            if (ns == oldS) continue;
            S[l][i] = ns;
            kind = 0;
        } else {
            i2 = rint_(k_);
            if (i2 == i) continue;
            int tmp = perm[l][i]; perm[l][i] = perm[l][i2]; perm[l][i2] = tmp;
            kind = 1;
        }
        long long nc = full_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            if (kind == 0) {
                S[l][i] = oldS;
            } else {
                int tmp = perm[l][i]; perm[l][i] = perm[l][i2]; perm[l][i2] = tmp;
            }
        }
    }
    return cost == 0;
}

static void save_best(void) {
    build_adj();
    int m = 0;
    for (int v = 0; v < N_; v++) {
        for (int q = 0; q < d_; q++) {
            int u = adj[v * d_ + q];
            if (u > v) { be_u[m] = v; be_v[m] = u; m++; }
        }
    }
    best_n = N_;
    best_m = m;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 2 || d_ > DMAX || D_ < 2 || start_n < 0) { printf("0 0\n"); return 0; }

    static const int ksel[8] = {1, 1, 2, 2, 2, 3, 3, 4};
    static const int k2sel[19] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30};
    double run_len = limit * 0.12;
    if (run_len < 0.5) run_len = 0.5;
    int target = start_n;

    while (1) {
        if (now_s() >= limit - 0.05) break;
        int k = ksel[rint_(8)];
        int k2 = k2sel[rint_(19)];
        int base2k = 2 * k * k2;
        int mmin = target / base2k + 1;
        if (mmin < 2) mmin = 2;
        int m = mmin + rint_(2 + mmin / 16);
        if ((long long)base2k * m > NMAX) continue;

        int r = 1 % m;
        if (k2 > 1 && m > 2) {
            for (int t = 0; t < 200; t++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod_(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        k_ = k; k2_ = k2; m_ = m; G_ = m * k2; N_ = 2 * k * G_; r_ = r;
        PW[0] = 1 % m;
        for (int t = 1; t < k2; t++) PW[t] = (int)((long long)PW[t - 1] * r % m);

        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < k_; i++) perm[l][i] = i;
            for (int i = k_ - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int tmp = perm[l][i]; perm[l][i] = perm[l][j]; perm[l][j] = tmp;
            }
            for (int i = 0; i < k_; i++) S[l][i] = rint_(G_);
        }

        double until = now_s() + run_len;
        if (until > limit) until = limit;
        if (run_sa(until)) {
            save_best();
            target = best_n;
        }
    }

    if (best_n == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", be_u[i], be_v[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine: bipartite edge-toggle annealer with vertex growth (from the parent).
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, cap_n, cap_w, N, W;
static int *deg, *adj, *side, *bestEu, *bestEv;
static u64 *bufA, *bufB;
static int *bvCur, *bvNew;
static int best_n = 0, best_m = 0;

static int isadj(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a * d_ + i] == b) return 1;
    return 0;
}
static void delE1(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d_ + i] == b) {
            adj[a * d_ + i] = adj[a * d_ + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}
static void addE(int a, int b) {
    adj[a * d_ + deg[a]++] = b;
    adj[b * d_ + deg[b]++] = a;
}
static void delE(int a, int b) { delE1(a, b); delE1(b, a); }

static long long bad_pairs(int *out) {
    u64 *cur = bufA, *alt = bufB;
    W = (N + 63) / 64;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)cap_w);
    for (int v = 0; v < N; v++) cur[(size_t)v * cap_w + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * cap_w;
            u64 *r = cur + (size_t)v * cap_w;
            for (int w = 0; w < W; w++) x[w] = r[w];
            for (int i = 0; i < deg[v]; i++) {
                u64 *q = cur + (size_t)adj[v * d_ + i] * cap_w;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) if (x[w] != r[w]) changed = 1;
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }
    long long total = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(r[w]);
        out[v] = N - pc;
        total += out[v];
    }
    return total;
}

static int pick_vertex(void) {
    if (rdbl() < 0.5) {
        for (int t = 0; t < 8; t++) {
            int v = rint_(N);
            if (bvCur[v] > 0) return v;
        }
    }
    return rint_(N);
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v * d_ + i];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    }
    best_n = N;
    best_m = m;
}

static void grow_pair(void) {
    side[N] = 0; deg[N] = 0;
    side[N + 1] = 1; deg[N + 1] = 0;
    N += 2;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int grow_max = argc > 5 ? atoi(argv[5]) : 60;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (d_ < 1 || D_ < 1 || n0 < 2 || n0 > 1000000 || grow_max < 0) {
        printf("0 0\n");
        return 0;
    }
    cap_n = n0 + 2 * grow_max + 2;
    cap_w = (cap_n + 63) / 64;
    deg = calloc(cap_n, sizeof(int));
    side = malloc(sizeof(int) * (size_t)cap_n);
    adj = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEu = malloc(sizeof(int) * (size_t)cap_n * d_);
    bestEv = malloc(sizeof(int) * (size_t)cap_n * d_);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bvCur = malloc(sizeof(int) * (size_t)cap_n);
    bvNew = malloc(sizeof(int) * (size_t)cap_n);
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB || !bvCur || !bvNew) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) continue;
        addE(u, v);
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    int *q = malloc(sizeof(int) * (size_t)cap_n);
    for (int s = 0; s < N; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v * d_ + i];
                if (side[u] == -1) { side[u] = 1 - side[v]; q[t++] = u; }
            }
        }
    }
    free(q);

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = bad_pairs(bvCur);
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = pick_vertex(), y = pick_vertex();
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs(bvNew);
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            int *tp = bvCur; bvCur = bvNew; bvNew = tp;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(bvCur); }
            }
        } else {
            delE(a, b);
            if (xa >= 0) addE(a, xa);
            if (xb >= 0) addE(b, xb);
        }
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _lift_in_c(d, D, seconds, seed, start_n):
    """Run the C group-lift annealer; returns (n, edges) of a valid lift larger than start_n, or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", start_n],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    avail = time_limit - 3.0

    # Phase 1: symmetry-reduced group-lift annealing in C.
    if d >= 2:
        lift_sec = max(0.5, 0.7 * avail - (time.monotonic() - t0))
        try:
            n1, e1 = _lift_in_c(d, D, lift_sec, rng.randrange(1, 1 << 30), best[0])
            consider(n1, e1)
        except Exception:
            pass  # keep the valid fallback

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
    c_budget = time_limit - 3.0 - (time.monotonic() - t0)
    if c_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
