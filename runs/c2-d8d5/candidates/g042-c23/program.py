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
#
# Warm start: argv[9] may carry a saved state "p0,p1,...;v0,v1,..." (perm then
# vol, layer-major). When the annealer fails it prints "STATE cost" and that
# state, so Python can resume the most promising lifts later instead of
# restarting them from scratch.
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

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

/* Parse cnt comma-separated ints in [0, maxv); advances *sp. */
static int parse_list(char **sp, int *out, int cnt, int maxv) {
    char *s = *sp;
    for (int i = 0; i < cnt; i++) {
        char *end;
        long v = strtol(s, &end, 10);
        if (end == s || v < 0 || v >= maxv) return 0;
        out[i] = (int)v;
        s = end;
        if (i < cnt - 1) {
            if (*s != ',') return 0;
            s++;
        }
    }
    *sp = s;
    return 1;
}

/* Check that every layer of p (d layers of k entries) is a permutation of 0..k-1. */
static int layers_ok(const int *p, int d, int k) {
    char *seen = calloc((size_t)k, 1);
    if (!seen) return 0;
    int ok = 1;
    for (int l = 0; l < d && ok; l++) {
        memset(seen, 0, (size_t)k);
        for (int i = 0; i < k; i++) {
            int v = p[l * k + i];
            if (seen[v]) { ok = 0; break; }
            seen[v] = 1;
        }
    }
    free(seen);
    return ok;
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

    int L = d_ * k_;
    perm = malloc(sizeof(int) * (size_t)L);
    vol = malloc(sizeof(int) * (size_t)L);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    int warm = 0;
    if (argc > 9 && argv[9][0] != '-') {
        char *s = argv[9];
        int ok = parse_list(&s, perm, L, k_) && *s == ';';
        if (ok) {
            s++;
            ok = parse_list(&s, vol, L, G_);
        }
        if (ok) ok = layers_ok(perm, d_, k_);
        warm = ok;
    }

    if (!warm) {
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
    }

    long long cost = eval_cost();
    double T0 = warm ? 2.0 : 6.0;
    const double T1 = 0.15;
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
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int old = vol[l * k_ + i];
            int nv = rint_(G_);
            if (nv == old) continue;
            vol[l * k_ + i] = nv;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                vol[l * k_ + i] = old;
            }
        }
    }

    if (cost != 0) {
        /* Unfinished: report the accepted state so Python can resume it. */
        printf("0 0\nSTATE %lld\n", cost);
        for (int i = 0; i < L; i++) printf(i ? ",%d" : "%d", perm[i]);
        printf(";");
        for (int i = 0; i < L; i++) printf(i ? ",%d" : "%d", vol[i]);
        printf("\n");
        return 0;
    }

    /* nbr is consistent with the accepted state because cost == 0 was just evaluated. */
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
_POOL_MAX = 6  # unfinished lifts kept for resumption


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


def _lift_in_c(d, D, k, m, k2, r, seconds, seed, state="-"):
    """Run the C lift annealer for one group (optionally resuming a saved state).

    Returns (n, edges, st): on success st is None; on failure st is (cost, state_text)
    describing the accepted annealer state, which can be passed back later.
    """
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r, state],
                    stdin_graph=None, timeout=seconds + 10.0)
    lines = out.strip().split("\n")
    if len(lines) >= 3 and lines[0].strip() == "0 0" and lines[1].startswith("STATE"):
        return 0, [], (int(lines[1].split()[1]), lines[2].strip())
    n, e = lib.parse_graph_text(out)
    return n, e, None


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

    # Phase 1: C lift annealing over groups. Fresh groups get random starts;
    # unfinished lifts with the lowest residual cost are resumed from their
    # saved state, so repeated slices accumulate on promising groups.
    lift_end = t0 + 0.8 * time_limit
    stats = {k: [0, 0] for k in _KS}   # [fresh trials, wins]
    frac = 0.08                         # target = best * (1 + frac)
    pool = []  # [cost, k, m, k2, r, state], best (lowest) cost first
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(4.0, max(1.0, 0.25 * remaining))
        seed = rng.randrange(1, 1 << 30)
        resumed = None
        if pool and rng.random() < 0.6:
            pool.sort(key=lambda p: p[0])
            resumed = pool.pop(0 if rng.random() < 0.5 else rng.randrange(len(pool)))
            _, k, m, k2, r, state = resumed
            if 2 * k * m * k2 <= best[0]:
                continue
        else:
            state = "-"
            k = _pick_k(rng, stats)
            target_n = int(best[0] * (1.0 + frac)) + 2
            g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
            if g is None:
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best[0]:
                continue
            stats[k][0] += 1
        try:
            n_, e_, st = _lift_in_c(d, D, k, m, k2, r, slice_s, seed, state)
        except RuntimeError:
            n_, e_, st = 0, [], None
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            best = (n_, e_)
            if resumed is None:
                stats[k][1] += 1
                frac = min(0.25, frac * 1.3)
            pool = [p for p in pool if 2 * p[1] * p[2] * p[3] > best[0]]
        else:
            if resumed is None:
                frac = max(0.003, frac * 0.85)
            if st is not None:
                pool.append([st[0], k, m, k2, r, st[1]])
                pool.sort(key=lambda p: p[0])
                del pool[_POOL_MAX:]

    # Phase 2: C toggle annealer tries to add vertex pairs to the best graph.
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
