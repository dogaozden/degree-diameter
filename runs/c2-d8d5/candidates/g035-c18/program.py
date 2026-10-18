import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: voltage-lift annealer over semidirect products Z_m x| Z_k2.
#
# A lift has K blocks per side, group G = m*k2, and d layers. Layer l is a
# permutation sigma_l of the K blocks plus a voltage g_{l,i} per block i.
# Edges: A(i,x) -- B(sigma_l(i), x*g_{l,i}) for every layer l. Left
# multiplication is an automorphism, so the diameter test only needs BFS from
# the 2K block representatives. Cost = unreached pairs + PEN * duplicate darts.
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

#define MAXD 32
#define MAXK 32
#define PEN 300

static int d_, D_, K_, M_, K2_, G_, N_;
static int pw_[65];
static int sig_[MAXD][MAXK], sinv_[MAXD][MAXK];
static int vol_[MAXD][MAXK], vin_[MAXD][MAXK];
static int *vis_, *queue_;
static int stamp_ = 0;
static clock_t C0;

static double elapsed(void) { return (double)(clock() - C0) / CLOCKS_PER_SEC; }

/* Semidirect product element a*K2+b, (a,b)(c,d) = (a + r^b c, b + d). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_;
    int c = y / K2_, d = y % K2_;
    int s = (int)(((long long)pw_[b] * c + a) % M_);
    return s * K2_ + (b + d) % K2_;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int t = (int)((long long)pw_[nb] * a % M_);
    int na = (M_ - t) % M_;
    return na * K2_ + nb;
}

/* Neighbour of lift vertex v through layer l. Blocks 0..K-1 are A, K..2K-1 are B. */
static int neighbor(int v, int l) {
    int blk = v / G_;
    int x = v - blk * G_;
    if (blk < K_) {
        int j = sig_[l][blk];
        return (K_ + j) * G_ + gmul(x, vol_[l][blk]);
    } else {
        int i = sinv_[l][blk - K_];
        return i * G_ + gmul(x, vin_[l][i]);
    }
}

static void rebuild_sinv(int l) {
    for (int i = 0; i < K_; i++) sinv_[l][sig_[l][i]] = i;
}

/* Sum over block representatives of the number of vertices at distance > D_. */
static long long eval_cost(void) {
    long long total = 0;
    int N = N_;
    for (int s = 0; s < 2 * K_; s++) {
        stamp_++;
        if (stamp_ == 0x7fffffff) {
            memset(vis_, 0, sizeof(int) * (size_t)N);
            stamp_ = 1;
        }
        int head = 0, tail = 0;
        int src = s * G_;
        vis_[src] = stamp_;
        queue_[tail++] = src;
        for (int depth = 0; depth < D_ && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = queue_[head++];
                for (int l = 0; l < d_; l++) {
                    int u = neighbor(v, l);
                    if (vis_[u] != stamp_) {
                        vis_[u] = stamp_;
                        queue_[tail++] = u;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long full_cost(void) {
    int dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig_[l][i] == sig_[l2][i] && vol_[l][i] == vol_[l2][i]) dup++;
    return eval_cost() + (long long)PEN * dup;
}

static void randomize(void) {
    for (int l = 0; l < d_; l++) {
        int perm[MAXK];
        for (int i = 0; i < K_; i++) perm[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K_; i++) sig_[l][i] = perm[i];
        rebuild_sinv(l);
        for (int i = 0; i < K_; i++) {
            int g = rint_(G_);
            vol_[l][i] = g;
            vin_[l][i] = ginv(g);
        }
    }
}

static void print_graph(void) {
    long long m = (long long)K_ * G_ * d_;
    printf("%d %lld\n", N_, m);
    for (int i = 0; i < K_; i++)
        for (int x = 0; x < G_; x++)
            for (int l = 0; l < d_; l++) {
                int j = sig_[l][i];
                int u = i * G_ + x;
                int v = (K_ + j) * G_ + gmul(x, vol_[l][i]);
                printf("%d %d\n", u, v);
            }
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
    if (d_ < 1 || d_ > MAXD || D_ < 1 || K_ < 1 || K_ > MAXK || M_ < 2 || K2_ < 1 || K2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    R %= M_;
    if (R < 0) R += M_;
    pw_[0] = 1 % M_;
    for (int t = 1; t <= K2_; t++) pw_[t] = (int)((long long)pw_[t - 1] * R % M_);
    if (pw_[K2_] != 1 % M_) { printf("0 0\n"); return 0; }
    G_ = M_ * K2_;
    N_ = 2 * K_ * G_;
    vis_ = calloc((size_t)N_, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N_);
    if (!vis_ || !queue_) { printf("0 0\n"); return 0; }

    C0 = clock();
    double seg = limit / 3.0;
    if (seg < 0.5) seg = 0.5;
    int found = 0;
    while (!found) {
        double el = elapsed();
        if (el >= limit) break;
        randomize();
        long long cost = full_cost();
        double segStart = el;
        double T0 = 2.0 + 0.05 * (double)cost;
        const double T1 = 0.3;
        while (1) {
            el = elapsed();
            if (el >= limit || el - segStart >= seg) break;
            double frac = (el - segStart) / seg;
            double T = T0 * pow(T1 / T0, frac);
            int l = rint_(d_);
            if (K_ >= 2 && rdbl() < 0.3) {
                int i1 = rint_(K_), i2 = rint_(K_ - 1);
                if (i2 >= i1) i2++;
                int t = sig_[l][i1]; sig_[l][i1] = sig_[l][i2]; sig_[l][i2] = t;
                rebuild_sinv(l);
                long long nc = full_cost();
                long long delta = nc - cost;
                if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                    cost = nc;
                } else {
                    t = sig_[l][i1]; sig_[l][i1] = sig_[l][i2]; sig_[l][i2] = t;
                    rebuild_sinv(l);
                }
            } else {
                int i = rint_(K_);
                int ov = vol_[l][i], ovi = vin_[l][i];
                int nv = rint_(G_ - 1);
                if (nv >= ov) nv++;
                vol_[l][i] = nv;
                vin_[l][i] = ginv(nv);
                long long nc = full_cost();
                long long delta = nc - cost;
                if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                    cost = nc;
                } else {
                    vol_[l][i] = ov;
                    vin_[l][i] = ovi;
                }
            }
            if (cost == 0) { found = 1; break; }
        }
    }
    if (found) print_graph();
    else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (from the parent).
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
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) with group Z_m x| Z_k2 of order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        r = None
        if k2 == 1:
            r = 1
        elif m >= 3:
            if k2 == 2 and rng.random() < 0.3 and math.gcd(m - 1, m) == 1 and pow(m - 1, 2, m) == 1 % m:
                r = m - 1
            else:
                for _ in range(60):
                    c = rng.randrange(2, m)
                    if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                        r = c
                        break
        if r is None:
            continue
        return m, k2, r
    return None


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C pair-growth annealer from a valid graph; returns parsed output (may be (0, []))."""
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

    # Phase 1: C voltage-lift search over semidirect products, with a bandit on base size k.
    lift_end = t0 + max(1.0, 0.6 * time_limit - 2.0)
    per_call = min(3.0, max(1.0, 0.05 * time_limit))
    ks = (1, 2, 3, 4, 5, 6, 8)
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}
    failures = 0

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    while failures < 5:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        goal = best[0] + max(2 * k, int(best[0] * rng.uniform(0.03, 0.15)))
        target = -(-goal // (2 * k))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        trials[k] += 1
        budget = min(per_call, remaining)
        try:
            out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            failures += 1
            continue
        if n > best[0]:
            before = best[0]
            consider(n, e)
            if best[0] > before:
                wins[k] += 1

    # Phase 2: C pair-growth annealer on the best valid graph found so far.
    c_budget = time_limit - (time.monotonic() - t0) - 6.0
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
