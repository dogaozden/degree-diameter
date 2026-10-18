"""Orbit-reduced voltage annealing for bi-Cayley lifts.

New in this version: a C engine (C_VOLT) that searches voltage lifts of a
bipartite base with k blocks per side over the semidirect product
Z_m x| Z_k2. Left multiplication by a group element is an automorphism of
the lift, so the distance cost only needs BFS from the 2k block
representatives, not from all vertices. Each voltage move updates only the
G neighbour entries of its dart (incremental), which makes a step about
an order of magnitude cheaper than the Python annealer. Once a valid lift
is found, the search moves to a slightly larger group order. The final phase
still uses the C vertex-growth annealer from the previous version.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (new): voltage annealer over Z_m x| Z_k2 with k blocks per side.
#
# Vertex (side, block, g) is encoded as index block*G + g, with side A
# blocks 0..k-1 and side B blocks k..2k-1. Dart (l, i) joins A-block i to
# B-block LY[l][i] with voltage S[l][i]: (i,x) ~ (j, x*s). Every vertex has
# degree d_. Cost = sum over the 2k representatives of the number of vertices
# not reached within D_ steps. Duplicate darts (same i, same j, same s) are
# penalised. A cost of zero with no duplicates is a simple valid graph.
# ----------------------------------------------------------------------------

C_VOLT = r"""
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

static int d_, D_, K_, M_, K2_, G_, NV_;
static int *powr, *invS, *S, *LY, *nb, *mark, *queue;
static int stamp_ = 0;

/* (a,b)*(c,e) = (a + r^b c, b + e) in Z_M x| Z_K2, element a*K2+b. */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, e = y % K2_;
    long long t = ((long long)a + (long long)powr[b] * c) % M_;
    return (int)(t * K2_ + (b + e) % K2_);
}

static void build_inv(void) {
    for (int s = 0; s < G_; s++) {
        int a = s / K2_, b = s % K2_;
        int nbb = (K2_ - b) % K2_;
        long long c = ((long long)M_ - ((long long)powr[nbb] * a) % M_) % M_;
        invS[s] = (int)(c * K2_ + nbb);
    }
}

/* Rewrites all neighbour entries that dart (l,i) controls. */
static void upd_layer_dart(int l, int i) {
    int j = LY[l * K_ + i], s = S[l * K_ + i], is = invS[s];
    for (int x = 0; x < G_; x++)
        nb[(i * G_ + x) * d_ + l] = (K_ + j) * G_ + gmul(x, s);
    for (int y = 0; y < G_; y++)
        nb[((K_ + j) * G_ + y) * d_ + l] = i * G_ + gmul(y, is);
}

static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (LY[l * K_ + i] == LY[l2 * K_ + i] && S[l * K_ + i] == S[l2 * K_ + i]) c++;
    return c;
}

/* Sum over the 2K representatives of unreached vertices within D_ steps. */
static long long cost_fn(void) {
    long long total = 0;
    for (int b = 0; b < 2 * K_; b++) {
        int src = b * G_;
        stamp_++;
        int h = 0, t = 0;
        queue[t++] = src;
        mark[src] = stamp_;
        for (int depth = 0; depth < D_ && h < t; depth++) {
            int end = t;
            while (h < end) {
                int v = queue[h++];
                for (int l = 0; l < d_; l++) {
                    int u = nb[v * d_ + l];
                    if (mark[u] != stamp_) { mark[u] = stamp_; queue[t++] = u; }
                }
            }
        }
        total += NV_ - t;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    int R = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 1 || K2_ < 1 || M_ > 100000 || K2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    G_ = M_ * K2_;
    NV_ = 2 * K_ * G_;
    if (NV_ > 200000) { printf("0 0\n"); return 0; }

    powr = malloc(sizeof(int) * K2_);
    invS = malloc(sizeof(int) * G_);
    S = malloc(sizeof(int) * d_ * K_);
    LY = malloc(sizeof(int) * d_ * K_);
    nb = malloc(sizeof(int) * (size_t)NV_ * d_);
    mark = calloc(NV_, sizeof(int));
    queue = malloc(sizeof(int) * NV_);
    if (!powr || !invS || !S || !LY || !nb || !mark || !queue) { printf("0 0\n"); return 0; }

    powr[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) powr[b] = (int)((long long)powr[b - 1] * (R % M_) % M_);
    if ((long long)powr[K2_ - 1] * (R % M_) % M_ != 1 % M_) { printf("0 0\n"); return 0; }
    build_inv();

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K_; i++) LY[l * K_ + i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = LY[l * K_ + i];
            LY[l * K_ + i] = LY[l * K_ + j];
            LY[l * K_ + j] = t;
        }
        for (int i = 0; i < K_; i++) S[l * K_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K_; i++) upd_layer_dart(l, i);

    const double PEN = 30.0, T0 = 4.0, T1 = 0.15;
    int dup = dup_count();
    long long cost = cost_fn();
    double score = (double)cost + PEN * dup;
    int found = (dup == 0 && cost == 0);

    clock_t c0 = clock();
    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (K_ >= 2 && rdbl() < 0.2) {
            int l = rint_(d_), i1 = rint_(K_), i2 = rint_(K_);
            if (i1 == i2) continue;
            int *row = LY + l * K_;
            int t = row[i1]; row[i1] = row[i2]; row[i2] = t;
            for (int i = 0; i < K_; i++) upd_layer_dart(l, i);
            int nd = dup_count();
            long long nc = cost_fn();
            double ns = (double)nc + PEN * nd;
            if (ns <= score || rdbl() < exp(-(ns - score) / T)) {
                score = ns; cost = nc; dup = nd;
            } else {
                t = row[i1]; row[i1] = row[i2]; row[i2] = t;
                for (int i = 0; i < K_; i++) upd_layer_dart(l, i);
            }
        } else {
            int l = rint_(d_), i = rint_(K_);
            int old = S[l * K_ + i];
            int nw = rint_(G_);
            if (nw == old) continue;
            S[l * K_ + i] = nw;
            upd_layer_dart(l, i);
            int nd = dup_count();
            long long nc = cost_fn();
            double ns = (double)nc + PEN * nd;
            if (ns <= score || rdbl() < exp(-(ns - score) / T)) {
                score = ns; cost = nc; dup = nd;
            } else {
                S[l * K_ + i] = old;
                upd_layer_dart(l, i);
            }
        }
        if (dup == 0 && cost == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }
    int m = K_ * G_ * d_;
    printf("%d %d\n", NV_, m);
    for (int v = 0; v < K_ * G_; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nb[v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (previous version): bipartite edge-toggle annealer with vertex
# growth. Used as the last phase to add vertices to the best valid graph.
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

_KS = (1, 2, 3, 4)


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


def _volt_search(d, D, k, m, k2, r, seconds, seed):
    """Run the C voltage annealer; returns (n, edges), with n = 0 on failure."""
    out = lib.run_c(C_VOLT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C vertex-growth annealer from a valid graph; returns (n, edges)."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _pick_k(rng, trials, wins):
    """Bandit-style choice of the number of base blocks per side."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())


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

    # Exact construction for D = 3 when d-1 is a prime power (calibration case).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: voltage lifts over semidirect products, searched in C.
    volt_end = t0 + max(2.0, 0.75 * time_limit - 2.0)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while True:
        remaining = volt_end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick_k(rng, trials, wins)
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 50 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        budget = min(remaining, rng.uniform(3.0, 7.0))
        trials[k] += 1
        before = best[0]
        try:
            cn, ce = _volt_search(d, D, k, m, k2, r, budget, rng.randrange(1, 1 << 30))
            if cn > 0:
                consider(cn, ce)
        except Exception:
            pass  # keep the valid fallback
        if best[0] > before:
            wins[k] += 1

    # Phase 2: C vertex-growth annealer from the best valid graph.
    grow_budget = time_limit * 0.88 - (time.monotonic() - t0) - 3.0
    if grow_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_budget,
                                rng.randrange(1, 1 << 30), 200)
            consider(cn, ce)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
