import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift search over Z_m x| Z_k2 (element a*k2+b, product
# (a,b)(c,e) = (a + r^b c, b + e)).
#
# Vertices: A_i x and B_t x for i, t in [0, k), x in G (index i*G+x, (k+t)*G+x).
# Layer l gives perm[l][i] and vol[l][i]:  A_i x ~ B_{perm[l][i]} (x * vol[l][i]).
# The graph is d-regular and bipartite. Left multiplication by G is an
# automorphism, so validity reduces to the 2k block representatives A_i e, B_t e.
# Cost = unreached vertices over those radius-D balls + penalty for repeated darts.
#
# Two search modes share the same state and move set:
#   mode 0: simulated annealing (single random move per step).
#   mode 1: NEW tabu min-conflicts search. Each step samples S random moves,
#           applies the best one that is not tabu (aspiration: a tabu move is
#           allowed if it beats the best cost seen). Moved darts stay tabu for
#           a short random tenure. After a stall, a small random kick is made.
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, m_, k2_, G_, N_;
static int *perm, *vol, *nbr, *pw, *queue_, *stamp;
static long long *tabu;
static int curstamp = 0;

typedef struct { int type, p1, p2, nv, ov; } Move;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int a2 = (int)((a + ((long long)pw[b] * c) % m_) % m_);
    int b2 = (b + e) % k2_;
    return a2 * k2_ + b2;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = gmul(x, s);
                int a = i * G + x, b = (k + t) * G + y;
                nbr[a * d + l] = b;
                nbr[b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = k_, d = d_, G = G_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
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

static void apply_mv(const Move *mv) {
    if (mv->type == 0) {
        vol[mv->p1] = mv->nv;
    } else {
        int t = perm[mv->p1];
        perm[mv->p1] = perm[mv->p2];
        perm[mv->p2] = t;
    }
}

static void undo_mv(const Move *mv) {
    if (mv->type == 0) {
        vol[mv->p1] = mv->ov;
    } else {
        int t = perm[mv->p1];
        perm[mv->p1] = perm[mv->p2];
        perm[mv->p2] = t;
    }
}

static Move rand_move(void) {
    Move mv;
    int l = rint_(d_), i = rint_(k_);
    int p = l * k_ + i;
    if (k_ >= 2 && rint_(3) == 0) {
        int i2 = rint_(k_ - 1);
        if (i2 >= i) i2++;
        mv.type = 1;
        mv.p1 = p;
        mv.p2 = l * k_ + i2;
        mv.nv = 0;
        mv.ov = 0;
    } else {
        mv.type = 0;
        mv.p1 = p;
        mv.p2 = p;
        mv.ov = vol[p];
        int nv;
        do { nv = rint_(G_); } while (nv == mv.ov && G_ > 1);
        mv.nv = nv;
    }
    return mv;
}

static int is_tabu(const Move *mv, long long step) {
    if (tabu[mv->p1] > step) return 1;
    if (mv->type == 1 && tabu[mv->p2] > step) return 1;
    return 0;
}

static void set_tabu(const Move *mv, long long until) {
    tabu[mv->p1] = until;
    if (mv->type == 1) tabu[mv->p2] = until;
}

static double elapsed(clock_t c0) {
    return (double)(clock() - c0) / CLOCKS_PER_SEC;
}

static long long anneal(double limit, clock_t c0) {
    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    while (cost > 0) {
        double el = elapsed(c0);
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);
        Move mv = rand_move();
        apply_mv(&mv);
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            undo_mv(&mv);
        }
    }
    return cost;
}

static long long tabu_search(double limit, clock_t c0) {
    const int S = 24;
    const int STALL = 3000;
    long long cost = eval_cost();
    long long bestc = cost;
    long long step = 0;
    int stall = 0;
    for (int i = 0; i < d_ * k_; i++) tabu[i] = 0;
    while (cost > 0) {
        if ((step & 15) == 0 && elapsed(c0) >= limit) break;
        step++;
        Move bm;
        long long bc = LLONG_MAX;
        int have = 0;
        for (int s = 0; s < S; s++) {
            Move mv = rand_move();
            apply_mv(&mv);
            long long c = eval_cost();
            undo_mv(&mv);
            if (is_tabu(&mv, step) && c >= bestc) continue;
            if (c < bc || (c == bc && rint_(2))) {
                bc = c;
                bm = mv;
                have = 1;
            }
        }
        if (!have) continue;
        apply_mv(&bm);
        cost = bc;
        set_tabu(&bm, step + 4 + rint_(8));
        if (cost < bestc) {
            bestc = cost;
            stall = 0;
        } else if (++stall > STALL) {
            for (int r = 0; r < 3; r++) {
                Move mv = rand_move();
                apply_mv(&mv);
            }
            cost = eval_cost();
            bestc = cost;
            stall = 0;
        }
    }
    return cost;
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
    int mode = argc > 9 ? atoi(argv[9]) : 1;
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
    tabu = calloc((size_t)d_ * k_, sizeof(long long));
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !tabu || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

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

    clock_t c0 = clock();
    long long cost = (mode == 0) ? anneal(limit, c0) : tabu_search(limit, c0);

    /* Rebuild nbr for the current state and confirm cost 0 before printing. */
    if (eval_cost() != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[v * d_ + l];
            if (u > v) pairs[cnt++] = (long long)v * N_ + u;
        }
    int cmp(const void *a, const void *b);
    qsort(pairs, (size_t)cnt, sizeof(long long), cmp);
    int uniq = 0;
    for (int i = 0; i < cnt; i++)
        if (i == 0 || pairs[i] != pairs[i - 1]) pairs[uniq++] = pairs[i];
    printf("%d %d\n", N_, uniq);
    for (int i = 0; i < uniq; i++)
        printf("%lld %lld\n", pairs[i] / N_, pairs[i] % N_);
    (void)cost;
    return 0;
}

int cmp(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth (from parent).
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

_KS = (1, 2, 3, 4, 5)
_MODES = (0, 1)


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


def _pick(rng, keys, stats):
    """Bandit choice: mostly exploit the best smoothed win rate, sometimes explore."""
    if rng.random() < 0.2:
        return rng.choice(keys)
    return max(keys, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, m, k2, r, seconds, seed, mode):
    """Run the C lift search (mode 0 = anneal, 1 = tabu) for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r, mode],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C toggle annealer from a valid graph; returns the parsed output (may be (0, []))."""
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

    # Phase 1: lift search over groups, with an adaptive target size.
    # Both search modes (annealing and tabu) are tried; the bandit learns which
    # one produces valid larger lifts for this (d, D).
    lift_end = t0 + 0.8 * time_limit
    kstats = {k: [0, 0] for k in _KS}
    mstats = {m: [0, 0] for m in _MODES}
    frac = 0.08  # target = best * (1 + frac)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        k = _pick(rng, _KS, kstats)
        mode = _pick(rng, _MODES, mstats)
        target_n = int(best[0] * (1.0 + frac)) + 2
        g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best[0]:
            continue
        kstats[k][0] += 1
        mstats[mode][0] += 1
        slice_s = min(10.0, max(2.0, 0.2 * remaining))
        if slice_s > remaining:
            slice_s = remaining
        try:
            n_, e_ = _lift_in_c(d, D, k, m, k2, r, slice_s,
                                rng.randrange(1, 1 << 30), mode)
        except RuntimeError:
            n_, e_ = 0, []
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            kstats[k][1] += 1
            mstats[mode][1] += 1
            best = (n_, e_)
            frac = min(0.25, frac * 1.3)
        else:
            frac = max(0.003, frac * 0.85)

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
