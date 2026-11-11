"""Lift annealer with warm-started base extension, plus a toggle annealer for vertex growth.

New in this version: warm-started lift extension. A valid lift over Z_m x| Z_k2 with
k base blocks is extended to k+1 blocks by inserting one block into each layer's
permutation (bijective insertion: the new source takes a random old target and the
old source is redirected to the new block), with random new voltages. The annealer
then starts from a nearly valid state instead of a random one, so the search can
climb from one group size to the next without restarting from scratch.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over Z_m x| Z_k2, with optional warm start.
#
# Vertices: A_i x and B_t x for i, t in [0, k) and x in G (index i*G+x, (k+t)*G+x).
# Layer l gives the permutation perm[l*k+i] and voltage vol[l*k+i]:
#     A_i x  ~  B_{perm[l*k+i]} (x * vol[l*k+i]).
# Each vertex gets one neighbour per layer. Left multiplication by G is an
# automorphism, so validity reduces to the 2k block representatives.
#
# Warm start (stdin): "n m" followed by m pairs whose flat values are
#     kold, perm (d*kold, layer-major with stride kold), vol (d*kold).
# New blocks are inserted by bijective insertion, so each layer's perm stays a
# permutation. Output after the edges: "PV k", then perm and vol (stride k).
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
    long long t = ((long long)pw[b] * c) % m_;
    int a2 = (int)((a + t) % m_);
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
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 64 || m_ < 2 || k2_ < 1) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;
    G_ = m_ * k2_;
    if ((long long)G_ * 2 * k_ > 200000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)(k2_ + 1));
    if (!pw) { printf("0 0\n"); return 0; }
    pw[0] = 1 % m_;
    for (int b = 1; b <= k2_; b++) pw[b] = (int)((long long)pw[b - 1] * r % m_);
    if (pw[k2_] != 1 % m_) { printf("0 0\n"); return 0; }

    perm = malloc(sizeof(int) * (size_t)d_ * k_);
    vol = malloc(sizeof(int) * (size_t)d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    stamp = calloc((size_t)N_, sizeof(int));
    if (!perm || !vol || !nbr || !queue_ || !stamp) { printf("0 0\n"); return 0; }

    /* optional warm start */
    int dummy_n = 0, in_m = 0;
    int *in = NULL, warm_kold = 0;
    if (scanf("%d %d", &dummy_n, &in_m) != 2) in_m = 0;
    if (in_m > 0) {
        int len = 2 * in_m;
        in = malloc(sizeof(int) * (size_t)len);
        int ok = (in != NULL);
        for (int i = 0; ok && i < len; i++)
            if (scanf("%d", &in[i]) != 1) ok = 0;
        if (ok && in[0] >= 1 && in[0] <= k_ && len >= 1 + 2 * d_ * in[0])
            warm_kold = in[0];
    }

    if (warm_kold > 0) {
        int ko = warm_kold, p = 1;
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < ko; i++) perm[l * k_ + i] = in[p++];
        for (int l = 0; l < d_; l++)
            for (int i = 0; i < ko; i++) vol[l * k_ + i] = in[p++];
        /* bijective insertion of new blocks i = ko .. k-1 into every layer */
        for (int i = ko; i < k_; i++) {
            for (int l = 0; l < d_; l++) {
                int j = rint_(i);
                perm[l * k_ + i] = perm[l * k_ + j];
                perm[l * k_ + j] = i;
            }
            for (int l = 0; l < d_; l++) vol[l * k_ + i] = rint_(G_);
        }
    } else {
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
    if (in) free(in);

    long long cost = eval_cost();
    const double T0 = (warm_kold > 0) ? 2.0 : 6.0, T1 = 0.15;
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

    if (cost != 0) { printf("0 0\n"); return 0; }

    build_nbr();
    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    if (!pairs) { printf("0 0\n"); return 0; }
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
    printf("PV %d\n", k_);
    for (int i = 0; i < d_ * k_; i++) printf("%d ", perm[i]);
    printf("\n");
    for (int i = 0; i < d_ * k_; i++) printf("%d ", vol[i]);
    printf("\n");
    free(pairs);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: bipartite edge-toggle annealer with vertex growth.
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

_KS = (1, 2, 3, 4, 5, 6)   # block counts for cold starts
_KMAX = 10                 # largest block count reached by warm extension


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
    """Bandit choice of base-block count k for cold starts (mostly exploit, sometimes explore)."""
    if rng.random() < 0.2:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _warm_stdin(kold, perm, vol):
    """Encode a lift state as the (n, pairs) stdin graph that the C lift engine reads."""
    flat = [kold] + list(perm) + list(vol)
    if len(flat) % 2:
        flat.append(0)
    return (0, [(flat[i], flat[i + 1]) for i in range(0, len(flat), 2)])


def _parse_pv(out, d):
    """Read the trailing 'PV k' block (perm and vol) printed by the lift engine; None if absent."""
    toks = out.split()
    if "PV" not in toks:
        return None
    i = toks.index("PV")
    try:
        kk = int(toks[i + 1])
        vals = [int(x) for x in toks[i + 2:i + 2 + 2 * d * kk]]
    except (ValueError, IndexError):
        return None
    if kk < 1 or len(vals) != 2 * d * kk:
        return None
    return kk, vals[:d * kk], vals[d * kk:]


def _lift_in_c(d, D, k, m, k2, r, seconds, seed, warm=None):
    """Run the C lift annealer (cold, or warm from a smaller lift). Returns (n, edges, lift_state)."""
    stdin_graph = None if warm is None else _warm_stdin(*warm)
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=stdin_graph, timeout=seconds + 10.0)
    n_, e_ = lib.parse_graph_text(out)
    return n_, e_, _parse_pv(out, d)


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

    # Phase 1: lift annealing. Two move types:
    #   warm: extend the best lift by one base block (same group), starting from its voltages;
    #   cold: a fresh random lift over a newly sampled group.
    lift_end = t0 + 0.82 * time_limit
    stats = {k: [0, 0] for k in _KS}   # [cold trials, cold wins]
    frac = 0.08                         # cold target = best * (1 + frac)
    best_lift = None                    # (k, m, k2, r, perm, vol) for the current best, if a lift
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.0:
            break
        run_seed = rng.randrange(1, 1 << 30)
        warm = None
        if best_lift is not None and best_lift[0] < _KMAX and rng.random() < 0.6:
            kold, m, k2, r, perm, vol = best_lift
            k = kold + 1
            warm = (kold, perm, vol)
            slice_s = min(15.0, max(3.0, 0.3 * remaining))
        else:
            k = _pick_k(rng, stats)
            target_n = int(best[0] * (1.0 + frac)) + 2
            g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
            if g is None:
                continue
            m, k2, r = g
            if 2 * k * m * k2 <= best[0]:
                continue
            stats[k][0] += 1
            slice_s = min(10.0, max(2.0, 0.2 * remaining))
        slice_s = min(slice_s, remaining)
        try:
            n_, e_, lift = _lift_in_c(d, D, k, m, k2, r, slice_s, run_seed, warm)
        except Exception:
            n_, e_, lift = 0, [], None
        if n_ > best[0] and lib.is_valid(n_, e_, d, D):
            best = (n_, e_)
            best_lift = (lift[0], m, k2, r, lift[1], lift[2]) if lift else None
            if warm is None:
                stats[k][1] += 1
                frac = min(0.25, frac * 1.3)
        elif warm is None:
            frac = max(0.003, frac * 0.85)

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
