import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (new): bi-Cayley lift annealer with BLOCK-SPLIT GROWTH.
#
# Group G = Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
# Blocks A_i, B_t (i, t < kc); vertex A_i x = i*G + x, B_t x = (kc+t)*G + x.
# Layer l has a permutation perm[l][i] and voltage vol[l][i]:
#     A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# Every vertex has exactly one neighbour per layer, so the graph is d-regular and
# bipartite. Left multiplication by G is an automorphism, so validity is checked
# on the 2*kc block representatives only (cost = unreached vertices + dup penalty).
#
# New move: block-split growth. When a valid lift is reached, every layer l picks a
# block i0 and sends A_i0 to a NEW block B_kc, while the new A_kc takes over the old
# target t. Each layer stays a permutation, so the graph stays d-regular. The order
# grows by 2G without restarting, and the annealer repairs the new block. This lets
# one run climb through many orders instead of sampling a fresh group per order.
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, m_, k2_, r_, G_, kc_, KCAP, NCAP;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp, *bestEu, *bestEv;
static int curstamp = 0, best_kc = 0, best_m = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (int)((a + ((long long)pw[b] * c) % m_) % m_);
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int k = kc_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * KCAP + i], s = vol[l * KCAP + i];
            for (int x = 0; x < G; x++) {
                int y = gmul(x, s);
                int a = i * G + x, b = (k + t) * G + y;
                nbr[(size_t)a * d + l] = b;
                nbr[(size_t)b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = kc_, d = d_, G = G_;
    int N = 2 * k * G;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * KCAP + i] == perm[l2 * KCAP + i] &&
                    vol[l1 * KCAP + i] == vol[l2 * KCAP + i])
                    dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D_) {
            int end = t;
            while (h < end) {
                int v = queue_[h++];
                const int *nv = nbr + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = nv[l];
                    if (stamp[u] != curstamp) {
                        stamp[u] = curstamp;
                        queue_[t++] = u;
                    }
                }
            }
            dist++;
        }
        cost += N - t;
    }
    return cost + 50 * dups;
}

/* Only call right after eval_cost() on the accepted state, so nbr matches it. */
static void save_best(void) {
    int N = 2 * kc_ * G_, d = d_, m = 0;
    for (int v = 0; v < N; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[(size_t)v * d + l];
            if (u > v) { bestEu[m] = v; bestEv[m] = u; m++; }
        }
    best_m = m;
    best_kc = kc_;
}

/* Split every layer: A_i0 goes to a new B block, the new A block takes the old target. */
static void grow_block(void) {
    int k = kc_;
    for (int l = 0; l < d_; l++) {
        int i0 = rint_(k);
        int t = perm[l * KCAP + i0];
        perm[l * KCAP + i0] = k;
        vol[l * KCAP + i0] = rint_(G_);
        perm[l * KCAP + k] = t;
        vol[l * KCAP + k] = rint_(G_);
    }
    kc_ = k + 1;
}

int main(int argc, char **argv) {
    if (argc < 10) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int k0 = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    int kmax = atoi(argv[9]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k0 < 1 || kmax < k0 || m_ < 2 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    r_ %= m_;
    if (r_ < 0) r_ += m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * kmax > 200000) { printf("0 0\n"); return 0; }

    KCAP = kmax;
    kc_ = k0;
    NCAP = 2 * KCAP * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r_ % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * KCAP);
    vol = malloc(sizeof(int) * (size_t)d_ * KCAP);
    nbr = malloc(sizeof(int) * (size_t)NCAP * d_);
    queue_ = malloc(sizeof(int) * (size_t)NCAP);
    stamp = calloc((size_t)NCAP, sizeof(int));
    bestEu = malloc(sizeof(int) * (size_t)NCAP * d_);
    bestEv = malloc(sizeof(int) * (size_t)NCAP * d_);
    if (!perm || !vol || !nbr || !queue_ || !stamp || !bestEu || !bestEv) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k0; i++) perm[l * KCAP + i] = i;
        for (int i = k0 - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * KCAP + i];
            perm[l * KCAP + i] = perm[l * KCAP + j];
            perm[l * KCAP + j] = t;
        }
        for (int i = 0; i < k0; i++) vol[l * KCAP + i] = rint_(G_);
    }

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;

        if (cost == 0) {
            cost = eval_cost();          /* rebuild nbr for the current state */
            if (cost == 0) {
                if (kc_ > best_kc) save_best();
                if (kc_ >= KCAP) break;
                grow_block();
                cost = eval_cost();
            }
            continue;
        }

        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(kc_);
        if (kc_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(kc_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * KCAP + i], *p2 = &perm[l * KCAP + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int old = vol[l * KCAP + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * KCAP + i] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * KCAP + i] = old;
            }
        }
    }

    if (best_kc == 0) { printf("0 0\n"); return 0; }
    int N = 2 * best_kc * G_;
    printf("%d %d\n", N, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (polish step).
# ----------------------------------------------------------------------------

C_SOURCE = r"""
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

static long long bad_pairs(void) {
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
    long long cnt = 0;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + (size_t)v * cap_w;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - cnt;
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
    if (!deg || !side || !adj || !bestEu || !bestEv || !bufA || !bufB) {
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
    long long cost = bad_pairs();
    if (cost == 0 && N > best_n) {
        save_best();
        if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = rint_(N), y = rint_(N);
            if (x == y || side[x] == side[y] || isadj(x, y)) continue;
            a = x; b = y;
            break;
        }
        if (a < 0) continue;

        int xa = -1, xb = -1;
        if (deg[a] == d_) { xa = adj[a * d_ + rint_(deg[a])]; delE(a, xa); }
        if (deg[b] == d_) { xb = adj[b * d_ + rint_(deg[b])]; delE(b, xb); }
        addE(a, b);

        long long nc = bad_pairs();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0 && N > best_n) {
                save_best();
                if (N + 2 <= cap_n) { grow_pair(); cost = bad_pairs(); }
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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _group_for(target_n, kc_guess, rng):
    """Group (m, k2, r) whose order G is about target_n / (2 * kc_guess)."""
    G = max(2, -(-target_n // (2 * kc_guess)))
    g = _sample_group(G, rng)
    if g is None:
        g = (G, 1, 1)
    return g


def _grow_lift_in_c(d, D, k0, m, k2, r, kmax, seconds, seed):
    """Run the block-split lift annealer; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", k0, m, k2, r, kmax],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the toggle annealer from a valid graph; returns the parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
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

    # Phase 1: block-split growth lifts. Each run starts from a small group lift and
    # grows its block count inside C, so one run climbs through several orders.
    lift_end = t0 + 0.85 * time_limit
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(remaining - 1.0, max(5.0, 0.22 * time_limit))
        target_n = int(best[0] * 1.04) + 2
        kc_guess = rng.choice([3, 4, 5, 6, 8, 10, 12])
        m, k2, r = _group_for(target_n, kc_guess, rng)
        G = m * k2
        kmax = max(2, -(-target_n // (2 * G)) + 2)
        kmax = min(kmax, max(1, 190000 // (2 * G)))
        k0 = min(rng.choice([1, 2, 2, 3]), kmax)
        try:
            n_, e_ = _grow_lift_in_c(d, D, k0, m, k2, r, kmax, slice_s,
                                     rng.randrange(1, 1 << 30))
        except RuntimeError:
            n_, e_ = 0, []
        consider(n_, e_)

    # Phase 2: toggle annealer tries to add vertex pairs to the best graph.
    c_budget = time_limit - (time.monotonic() - t0) - 4.0
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
