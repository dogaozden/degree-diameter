import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (kept from the parent): bipartite edge-toggle annealer with vertex
# growth. Used as a final polishing step on the best valid graph.
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
# C engine 2 (new): bi-Cayley lift search over Z_m x| Z_k2.
#
# NEW IDEA: a group lift with a semiregular group action is vertex-transitive
# on each side's orbit, so the diameter condition only needs BFS from the 2k
# base representatives (block i, identity element). Each annealing evaluation
# is therefore 2k BFS runs of O(N d) instead of an O(N^2 d D / 64) bitset
# sweep, which makes the search roughly two orders of magnitude faster than the
# Python numpy version. The final output is re-checked by BFS from every vertex.
#
# Model: k base vertices per side. Layer l (l = 0..d-1) is a bijection
# i -> layers[l][i]; dart (i, l) joins A_{i,g} to B_{j,g*s} with j = layers[l][i]
# and s = S[l][i]. Each vertex then has degree d. Duplicate darts (same i, j, s)
# give parallel edges and are penalised.
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

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int P_ = 20000;
static int *mulT, *invT, *pw, *layers, *pinv, *S, *queue, *stamp;
static int curStamp = 0;

static int groupmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    long long aa = ((long long)a + (long long)pw[b] * c) % m_;
    return (int)(aa * k2_ + (b + e) % k2_);
}

static inline int nbr(int v, int l) {
    int G = G_, k = k_;
    int blk = v / G, g = v - blk * G;
    if (blk < k) {
        int idx = l * k + blk;
        return (k + layers[idx]) * G + mulT[(size_t)g * G + S[idx]];
    } else {
        int j = blk - k;
        int i = pinv[l * k + j];
        int idx = l * k + i;
        return i * G + mulT[(size_t)g * G + invT[S[idx]]];
    }
}

static int bfs_unreached(int src) {
    curStamp++;
    int h = 0, t = 0;
    queue[t++] = src;
    stamp[src] = curStamp;
    for (int dep = 0; dep < D_ && h < t; dep++) {
        int end = t;
        for (; h < end; h++) {
            int v = queue[h];
            for (int l = 0; l < d_; l++) {
                int u = nbr(v, l);
                if (stamp[u] != curStamp) { stamp[u] = curStamp; queue[t++] = u; }
            }
        }
    }
    return N_ - t;
}

static int dupcount(void) {
    int K = d_ * k_, c = 0;
    for (int a = 0; a < K; a++) {
        int ia = a % k_, ja = layers[a], sa = S[a];
        for (int b = a + 1; b < K; b++) {
            if (b % k_ == ia && layers[b] == ja && S[b] == sa) c++;
        }
    }
    return c;
}

static long long total_cost(void) {
    long long c = 0;
    for (int i = 0; i < 2 * k_; i++) c += bfs_unreached(i * G_);
    c += (long long)N_ * dupcount();
    return c;
}

static void fixPinv(int l) {
    for (int i = 0; i < k_; i++) pinv[l * k_ + layers[l * k_ + i]] = i;
}

static void randomize(void) {
    for (int l = 0; l < d_; l++) {
        int *p = layers + l * k_;
        for (int i = 0; i < k_; i++) p[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        fixPinv(l);
    }
    for (int x = 0; x < d_ * k_; x++) S[x] = rint_(G_);
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
    if (d_ < 1 || D_ < 1 || k_ < 1 || k_ > 16 || d_ > 64 || m_ < 1 || k2_ < 1) {
        printf("0 0\n"); return 0;
    }
    long long Gl = (long long)m_ * k2_;
    if (Gl > 2500) { printf("0 0\n"); return 0; }
    if (m_ == 1) r_ = 0;
    if (r_ < 0 || (m_ > 1 && r_ >= m_)) { printf("0 0\n"); return 0; }
    G_ = (int)Gl;
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * k2_);
    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * G_);
    layers = malloc(sizeof(int) * d_ * k_);
    pinv = malloc(sizeof(int) * d_ * k_);
    S = malloc(sizeof(int) * d_ * k_);
    queue = malloc(sizeof(int) * N_);
    stamp = calloc(N_, sizeof(int));
    if (!pw || !mulT || !invT || !layers || !pinv || !S || !queue || !stamp) {
        printf("0 0\n"); return 0;
    }

    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (int)(((long long)pw[b - 1] * r_) % m_);

    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            mulT[(size_t)x * G_ + y] = groupmul(x, y);
    for (int x = 0; x < G_; x++) {
        invT[x] = -1;
        for (int y = 0; y < G_; y++)
            if (mulT[(size_t)x * G_ + y] == 0) { invT[x] = y; break; }
        if (invT[x] < 0) { printf("0 0\n"); return 0; }
    }

    randomize();
    long long cost = total_cost();
    long long runBest = cost, lastImp = 0;
    const double T0 = 0.01 * N_ + 1.0, T1 = 0.3;
    clock_t c0 = clock();
    double el = 0.0, T = T0;
    long long it = 0;

    while (cost > 0) {
        if ((it & 127) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            T = T0 * pow(T1 / T0, el / limit);
        }
        it++;
        if (it - lastImp > P_) {
            randomize();
            cost = total_cost();
            runBest = cost;
            lastImp = it;
            continue;
        }
        int l = rint_(d_);
        if (k_ >= 2 && rdbl() < 0.3) {
            int i1 = rint_(k_), i2 = rint_(k_);
            if (i1 == i2) continue;
            int a = l * k_ + i1, b = l * k_ + i2;
            int t = layers[a]; layers[a] = layers[b]; layers[b] = t;
            fixPinv(l);
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = layers[a]; layers[a] = layers[b]; layers[b] = t;
                fixPinv(l);
            }
        } else {
            int idx = l * k_ + rint_(k_);
            int old = S[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            S[idx] = nv;
            long long nc = total_cost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[idx] = old;
            }
        }
        if (cost < runBest) { runBest = cost; lastImp = it; }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    /* Safety: verify from every vertex, not only the base representatives. */
    long long bad = 0;
    for (int v = 0; v < N_ && bad == 0; v++) bad += bfs_unreached(v);
    if (bad != 0 || dupcount() != 0) { printf("0 0\n"); return 0; }

    int nE = d_ * k_ * G_;
    printf("%d %d\n", N_, nE);
    for (int v = 0; v < k_ * G_; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr(v, l));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_MAX_G = 2400


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_of_order(G, rng):
    """Return (m, k2, r) with m * k2 == G for Z_m x| Z_k2 (r^k2 = 1 mod m, gcd(r, m) = 1), or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m == 1:
            return 1, k2, 0
        if k2 == 1:
            return m, 1, 1 % m
        for _ in range(80):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _lift_search(d, D, k, G, rng, budget):
    """Run the C lift search for a group of order G with k base vertices per side.

    Returns (n, edges) on success, or None.
    """
    g = _group_of_order(G, rng)
    if g is None:
        return None
    m, k2, r = g
    out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                    timeout=budget + 20.0)
    n, edges = lib.parse_graph_text(out)
    return (n, edges) if n > 0 else None


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C annealer from a valid graph; returns the parsed output (may be (0, []))."""
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

    # Phase 1: C bi-Cayley lift search. Each call targets a group order just
    # above the current best, so every success raises the bar.
    lift_end = t0 + max(1.0, min(0.7 * time_limit, time_limit - 12.0))
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        left = lift_end - time.monotonic()
        if left < 0.5:
            break
        k = pick_k()
        base_G = best[0] // (2 * k)
        G = base_G + 1 + rng.randrange(0, max(1, base_G // 40))
        if G > _MAX_G:
            continue
        trials[k] += 1
        try:
            res = _lift_search(d, D, k, G, rng, min(2.5, left))
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: C annealer grows the best valid graph by vertex pairs.
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
