import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New idea: orbit-reduced lift search.
#
# A group lift over G = Z_m x| Z_k2 with base layers (k blocks per side, d
# perfect matchings between them, voltages in G) is G-symmetric under LEFT
# multiplication: (i, x) -> (i, y x) is an automorphism. So the diameter test
# only needs BFS from the 2k identity vertices (i, e), one per base block.
# Cost = unreached pairs from those 2k sources, plus a penalty for duplicate
# darts. Each evaluation is a few BFS passes instead of a full all-pairs
# bitset computation, so the C annealer tests far more groups and voltages.
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
static int ri(int n) { return (int)(rnd() % (u64)n); }
static double rdb(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int *MUL, *pw, *perm, *vol, *adj, *cnt, *stamp, *dist_, *queue_;
static int curStamp = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static void build_group(void) {
    pw = malloc(sizeof(int) * (size_t)k2_);
    long long p = 1 % m_;
    for (int b = 0; b < k2_; b++) {
        pw[b] = (int)p;
        p = (p * r_) % m_;
    }
    MUL = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / k2_, b = x % k2_;
        for (int y = 0; y < G_; y++) {
            int c = y / k2_, e = y % k2_;
            long long na = ((long long)a + (long long)pw[b] * c) % m_;
            int nb = (b + e) % k2_;
            MUL[(size_t)x * G_ + y] = (int)(na * k2_ + nb);
        }
    }
}

/* Fill adj: A-vertex i*G+x has neighbour (k+j)*G + x*s for each layer l,
   where j = perm[l][i], s = vol[l][i]. B-vertices receive exactly d darts. */
static void build_adj(void) {
    int k = k_, G = G_, d = d_;
    for (int w = 0; w < N_; w++) cnt[w] = 0;
    for (int i = 0; i < k; i++)
        for (int x = 0; x < G; x++) {
            int v = i * G + x;
            for (int l = 0; l < d; l++) {
                int j = perm[l * k + i];
                int s = vol[l * k + i];
                int w = (k + j) * G + MUL[(size_t)x * G + s];
                adj[v * d + l] = w;
                adj[w * d + cnt[w]] = v;
                cnt[w]++;
            }
        }
}

static int dup_count(void) {
    int dups = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (perm[l * k_ + i] == perm[l2 * k_ + i] && vol[l * k_ + i] == vol[l2 * k_ + i])
                    dups++;
    return dups;
}

/* Zero iff the lift is simple, bipartite, d-regular and of diameter <= D_. */
static long long eval_cost(void) {
    build_adj();
    long long cost = 0;
    int NB = 2 * k_;
    for (int b = 0; b < NB; b++) {
        int src = b * G_;
        curStamp++;
        int h = 0, t = 0;
        queue_[t++] = src;
        stamp[src] = curStamp;
        dist_[src] = 0;
        while (h < t) {
            int v = queue_[h++];
            if (dist_[v] >= D_) continue;
            const int *nb = adj + (size_t)v * d_;
            for (int e = 0; e < d_; e++) {
                int u = nb[e];
                if (stamp[u] != curStamp) {
                    stamp[u] = curStamp;
                    dist_[u] = dist_[v] + 1;
                    queue_[t++] = u;
                }
            }
        }
        cost += N_ - t;
    }
    cost += 40LL * dup_count();
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1 || r_ < 1 || r_ >= m_ ||
        (long long)m_ * k2_ > 4000 || (long long)k_ * m_ * k2_ > 200000 ||
        gcd_(r_, m_) != 1) {
        printf("0 0\n");
        return 0;
    }
    long long pk = 1 % m_;
    for (int b = 0; b < k2_; b++) pk = (pk * r_) % m_;
    if (pk != 1 % m_) { printf("0 0\n"); return 0; }

    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    build_group();
    int nd = d_ * k_;
    perm = malloc(sizeof(int) * (size_t)nd);
    vol = malloc(sizeof(int) * (size_t)nd);
    adj = malloc(sizeof(int) * (size_t)N_ * d_);
    cnt = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    dist_ = malloc(sizeof(int) * (size_t)N_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    if (!perm || !vol || !adj || !cnt || !stamp || !dist_ || !queue_) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) perm[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = ri(i + 1);
            int t = perm[l * k_ + i];
            perm[l * k_ + i] = perm[l * k_ + j];
            perm[l * k_ + j] = t;
        }
    }
    for (int t = 0; t < nd; t++) vol[t] = ri(G_);

    long long cost = eval_cost();
    const double T0 = 10.0, T1 = 0.3;
    clock_t c0 = clock();
    int found = (cost == 0);

    while (!found) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        int l = ri(d_), i = ri(k_);
        long long c2;
        if (k_ >= 2 && (rnd() & 1)) {
            int i2 = ri(k_ - 1);
            if (i2 >= i) i2++;
            int a = l * k_ + i, b = l * k_ + i2;
            int t = perm[a]; perm[a] = perm[b]; perm[b] = t;
            c2 = eval_cost();
            if (c2 <= cost || rdb() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                t = perm[a]; perm[a] = perm[b]; perm[b] = t;
            }
        } else {
            int idx = l * k_ + i;
            int old = vol[idx];
            int nw = ri(G_);
            if (nw == old) continue;
            vol[idx] = nw;
            c2 = eval_cost();
            if (c2 <= cost || rdb() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                vol[idx] = old;
            }
        }
        if (cost == 0) { found = 1; break; }
    }

    if (!found) { printf("0 0\n"); return 0; }
    build_adj();
    int NA = k_ * G_;
    printf("%d %lld\n", N_, (long long)NA * d_);
    for (int v = 0; v < NA; v++)
        for (int e = 0; e < d_; e++)
            printf("%d %d\n", v, adj[v * d_ + e]);
    return 0;
}
"""


# Vertex-growth annealer (general edge toggles with bitset ball expansion).
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

_KS = (2, 3, 4, 5, 6, 7)


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


def _lift_in_c(d, D, k, m, k2, r, seconds, seed):
    """Run the orbit-reduced lift annealer; returns (n, edges), or (0, []) on failure."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the vertex-growth annealer from a valid graph; returns (n, edges)."""
    out = lib.run_c(C_GROW, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def _lift_phase(d, D, best, rng, end):
    """Search group lifts with growing order; returns the best valid graph found."""
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    failures = 0
    while failures < 6:
        remaining = end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, base // 16 + 2))
        g = _sample_group(target, rng)
        if g is None:
            failures += 1
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        seconds = min(remaining - 0.5, 2.0 + 2.0 * rng.random())
        if seconds < 0.5:
            break
        trials[k] += 1
        try:
            n2, e2 = _lift_in_c(d, D, k, m, k2, r, seconds, rng.randrange(1, 1 << 30))
        except Exception:
            failures += 1
            continue
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
            wins[k] += 1
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    # Exact construction for D = 3: returns immediately when d - 1 is a prime power.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: orbit-reduced group-lift search (C).
    if d >= 3 and D >= 2:
        lift_end = t0 + 0.7 * time_limit - 1.0
        best = _lift_phase(d, D, best, rng, lift_end)

    # Phase 2: vertex growth from the best valid graph (C).
    grow_budget = time_limit - (time.monotonic() - t0) - 6.0
    if grow_budget >= 1.0:
        try:
            cn, ce = _grow_in_c(best[0], best[1], d, D, grow_budget,
                                rng.randrange(1, 1 << 30), 200)
            if cn > best[0] and lib.is_valid(cn, ce, d, D):
                best = (cn, ce)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
