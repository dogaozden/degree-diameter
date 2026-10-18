import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over the semidirect product
# Z_m x| Z_k2 (element a*k2+b, product (a,b)(c,e) = (a + r^b c, b + e)).
#
# Vertices: A_i x and B_t x for i, t in [0, k) and x in G (index i*G+x, (k+t)*G+x).
# Layer l gives the permutation perm[l][i] and voltage vol[l][i]:
#     A_i x  ~  B_{perm[l][i]} (x * vol[l][i]).
# Each vertex gets exactly one neighbour per layer, so the graph is d-regular
# and bipartite. Left multiplication by G is an automorphism, so validity
# reduces to checking the 2k block representatives A_i e and B_t e.
# ----------------------------------------------------------------------------

C_LIFT = r"""
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static int curstamp = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (a + (pw[b] * c) % m_) % m_;
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void set_dart(int l, int i) {
    int k = k_, G = G_, d = d_;
    int t = perm[l * k + i], s = vol[l * k + i];
    for (int x = 0; x < G; x++) {
        int y = gmul(x, s);
        int a = i * G + x, b = (k + t) * G + y;
        nbr[a * d + l] = b;
        nbr[b * d + l] = a;
    }
}

static void set_all_darts(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++) set_dart(l, i);
}

static long long eval_cost(void) {
    int k = k_, d = d_, D = D_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G_;
        curstamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curstamp;
        int dist = 0;
        while (h < t && dist < D) {
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

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = atoi(argv[8]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    r %= m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) vol[l * k_ + i] = rint_(G_);
    }

    set_all_darts();
    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *p1 = &perm[l * k_ + i], *p2 = &perm[l * k_ + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
            set_dart(l, i);
            set_dart(l, i2);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
                set_dart(l, i);
                set_dart(l, i2);
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            set_dart(l, i);
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
                set_dart(l, i);
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            if (u > v) pairs[cnt++] = (long long)v * N_ + u;
        }
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp_ll);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N_, pairs[i] % N_);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: unstructured bipartite regular-graph annealer.
#
# Starts from a circulant d-regular bipartite graph on 2*s0 vertices, randomises
# it with double-edge swaps (these keep the graph simple, bipartite and
# d-regular), then anneals the number of unordered-pair-like defects
# (ordered pairs at distance > D) to zero with the same swap move. Whenever the
# defect count reaches zero the graph is saved and grown by one A-B vertex
# pair (each new vertex takes d edges by splitting d existing edges with
# distinct endpoints), then annealing continues.
# ----------------------------------------------------------------------------

C_REG = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 3072
#define STR 48
#define MAXD 16

typedef uint64_t u64;
static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, N, nA, err_;
static int nbr[MAXV * MAXD];
static int listA[MAXV];
static unsigned char adjm[MAXV * MAXV];
static u64 bufA[MAXV * STR], bufB[MAXV * STR];
static int bu[MAXV * 8], bv[MAXV * 8];
static int best_N = 0, best_E = 0;

static void rep(int v, int old, int nw) {
    int *p = nbr + v * d_;
    for (int j = 0; j < d_; j++) if (p[j] == old) { p[j] = nw; return; }
    err_ = 1;
}

/* Replace edges (x1,y1),(x2,y2) by (x1,y2),(x2,y1). Caller checks validity. */
static void swap_apply(int x1, int y1, int x2, int y2) {
    rep(x1, y1, y2); rep(y1, x1, x2);
    rep(x2, y2, y1); rep(y2, x2, x1);
    adjm[x1 * MAXV + y1] = 0; adjm[y1 * MAXV + x1] = 0;
    adjm[x2 * MAXV + y2] = 0; adjm[y2 * MAXV + x2] = 0;
    adjm[x1 * MAXV + y2] = 1; adjm[y2 * MAXV + x1] = 1;
    adjm[x2 * MAXV + y1] = 1; adjm[y1 * MAXV + x2] = 1;
}

static long long cost_fn(void) {
    int W = (N + 63) >> 6;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) {
        u64 *r = cur + v * STR;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = nxt + v * STR;
            const u64 *r = cur + v * STR;
            for (int w = 0; w < W; w++) x[w] = r[w];
            const int *p = nbr + v * d_;
            for (int j = 0; j < d_; j++) {
                const u64 *q = cur + p[j] * STR;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            if (!changed)
                for (int w = 0; w < W; w++) if (x[w] != r[w]) { changed = 1; break; }
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = cur + v * STR;
        for (int w = 0; w < W; w++) tot += __builtin_popcountll(r[w]);
    }
    return (long long)N * N - tot;
}

static void save_best(void) {
    int m = 0;
    for (int v = 0; v < N; v++) {
        const int *p = nbr + v * d_;
        for (int j = 0; j < d_; j++)
            if (p[j] > v) { bu[m] = v; bv[m] = p[j]; m++; }
    }
    best_N = N;
    best_E = m;
}

static void init_circ(int s) {
    N = 2 * s;
    nA = s;
    for (int i = 0; i < s; i++) {
        listA[i] = i;
        for (int j = 0; j < d_; j++) {
            int b = s + (i + j) % s;
            nbr[i * d_ + j] = b;
            adjm[i * MAXV + b] = 1;
            adjm[b * MAXV + i] = 1;
        }
    }
    for (int t = 0; t < s; t++)
        for (int j = 0; j < d_; j++)
            nbr[(s + t) * d_ + j] = (t - j + s) % s;
}

/* Add one A vertex a = N and one B vertex b = N+1, each of degree d_. */
static int grow(void) {
    if (nA < d_ || N + 2 > MAXV) return 0;
    int a = N, b = N + 1;
    int xs[MAXD], ys[MAXD];
    for (int tries = 0; tries < 4000; tries++) {
        for (int k = 0; k < d_; k++) {
            int x = listA[rint_(nA)];
            xs[k] = x;
            ys[k] = nbr[x * d_ + rint_(d_)];
        }
        int ok = 1;
        for (int k = 0; k < d_ && ok; k++)
            for (int l = k + 1; l < d_; l++)
                if (xs[k] == xs[l] || ys[k] == ys[l]) { ok = 0; break; }
        if (!ok) continue;
        for (int k = 0; k < d_; k++) {
            int x = xs[k], y = ys[k];
            rep(x, y, b);
            rep(y, x, a);
            adjm[x * MAXV + y] = 0; adjm[y * MAXV + x] = 0;
            adjm[x * MAXV + b] = 1; adjm[b * MAXV + x] = 1;
            adjm[a * MAXV + y] = 1; adjm[y * MAXV + a] = 1;
            nbr[a * d_ + k] = y;
            nbr[b * d_ + k] = x;
        }
        listA[nA++] = a;
        N += 2;
        return 1;
    }
    return 0;
}

static void on_zero(int gmax, int *grows) {
    if (N > best_N) save_best();
    if (*grows < gmax && grow()) (*grows)++;
}

int main(int argc, char **argv) {
    if (argc < 7) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    int s0 = atoi(argv[5]), gmax = atoi(argv[6]);
    if (d_ < 3 || d_ > MAXD || D_ < 2 || s0 < d_ || gmax < 0 || 2 * s0 + 2 * gmax + 2 > MAXV) {
        printf("0 0\n");
        return 0;
    }

    init_circ(s0);
    for (long long it = 0, lim = 10LL * s0 * d_; it < lim; it++) {
        int x1 = listA[rint_(nA)], j1 = rint_(d_), y1 = nbr[x1 * d_ + j1];
        int x2 = listA[rint_(nA)], j2 = rint_(d_), y2 = nbr[x2 * d_ + j2];
        if (x1 == x2 || y1 == y2 || adjm[x1 * MAXV + y2]) continue;
        swap_apply(x1, y1, x2, y2);
    }

    const double T0 = 8.0, T1 = 0.4;
    int grows = 0;
    long long cost = cost_fn();
    clock_t c0 = clock();
    if (cost == 0) {
        int before = N;
        on_zero(gmax, &grows);
        if (N != before) cost = cost_fn();
    }

    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit || err_) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int x1 = listA[rint_(nA)], j1 = rint_(d_), y1 = nbr[x1 * d_ + j1];
        int x2 = listA[rint_(nA)], j2 = rint_(d_), y2 = nbr[x2 * d_ + j2];
        if (x1 == x2 || y1 == y2 || adjm[x1 * MAXV + y2]) continue;

        swap_apply(x1, y1, x2, y2);
        long long nc = cost_fn();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) {
                int before = N;
                on_zero(gmax, &grows);
                if (N != before) cost = cost_fn();
            }
        } else {
            swap_apply(x1, y2, x2, y1);
        }
    }

    if (best_N == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_N, best_E);
    for (int i = 0; i < best_E; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5)


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


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _reg_in_c(d, D, seed, seconds, s0, gmax):
    """Run the unstructured regular-graph annealer; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_REG, [d, D, seed, f"{seconds:.2f}", s0, gmax],
                    stdin_graph=None, timeout=seconds + 5.0)
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

    # Phase 1 (about 20% of the budget): structured lift annealing gives a strong fallback.
    if d >= 3:
        lift_end = t0 + 0.2 * time_limit
        stats = {k: [0, 0] for k in _KS}   # [trials, wins]
        frac = 0.08
        while True:
            remaining = lift_end - time.monotonic()
            if remaining < 1.0:
                break
            k = _pick_k(rng, stats)
            target_n = int(best[0] * (1.0 + frac)) + 2
            g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
            if g is None:
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best[0]:
                continue
            stats[k][0] += 1
            slice_s = min(3.0, max(1.0, 0.25 * remaining))
            try:
                n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s, rng.randrange(1, 1 << 30))
            except RuntimeError:
                n_, e_ = 0, []
            if n_ > best[0] and lib.is_valid(n_, e_, d, D):
                stats[k][1] += 1
                best = (n_, e_)
                frac = min(0.25, frac * 1.3)
            else:
                frac = max(0.003, frac * 0.85)

    # Phase 2 (bold change, most of the budget): unstructured anneal of random
    # regular bipartite graphs, grown one vertex pair at a time from a smaller size.
    if d >= 3:
        elapsed = time.monotonic() - t0
        reg_budget = 0.85 * time_limit - elapsed - 4.0
        s0 = best[0] // 2 - 20
        if reg_budget >= 3.0 and s0 >= d + 1:
            gmax = max(0, min(200, (3070 - 2 * s0) // 2))
            try:
                n_, e_ = _reg_in_c(d, D, rng.randrange(1, 1 << 30), reg_budget, s0, gmax)
                consider(n_, e_)
            except Exception:
                pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
