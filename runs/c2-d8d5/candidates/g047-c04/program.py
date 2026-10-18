import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over an explicit finite group.
#
# Groups are built inside C from a family code:
#   type 0: metacyclic Z_p1 x|_p3 Z_p2  (element a*p2+b, (a,b)(c,e) = (a+r^b c, b+e))
#   type 1: Heisenberg group over Z_p1  (element (a*n+b)*n+c, (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b'))
#
# Vertices: A_i x = i*G+x and B_t x = (k+t)*G+x. Layer l gives perm[l][i] and
# vol[l][i] with A_i x ~ B_{perm[l][i]} (x * vol[l][i]). Each vertex has one
# neighbour per layer, so the graph is d-regular (before duplicate removal) and
# bipartite. Left multiplication by G is an automorphism, so validity reduces to
# the 2k block representatives A_i e and B_t e. Cost = total unreached vertices
# over those radius-D balls, plus a penalty for repeated darts.
# The annealer uses several reheating cycles.
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

static int d_, D_, k_, G_, N_;
static int *gt, *perm, *vol, *nbr, *queue_, *stamp;
static int curstamp = 0;

static int build_group(int type, int p1, int p2, int p3) {
    if (type == 0) {
        int m = p1, k2 = p2, r = p3;
        if (m < 2 || k2 < 1 || r < 0 || r >= m) return 0;
        long long G = (long long)m * k2;
        if (G > 2000) return 0;
        G_ = (int)G;
        int *pw = malloc(sizeof(int) * (size_t)(k2 + 1));
        if (!pw) return 0;
        pw[0] = 1 % m;
        for (int b = 1; b <= k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
        if (pw[k2] != 1 % m) { free(pw); return 0; }
        gt = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
        if (!gt) { free(pw); return 0; }
        for (int x = 0; x < G_; x++) {
            int a = x / k2, b = x % k2;
            for (int y = 0; y < G_; y++) {
                int c = y / k2, e = y % k2;
                int a2 = (a + (int)((long long)pw[b] * c % m)) % m;
                int b2 = (b + e) % k2;
                gt[(size_t)x * G_ + y] = a2 * k2 + b2;
            }
        }
        free(pw);
        return 1;
    } else if (type == 1) {
        int n = p1;
        if (n < 2 || n * n * n > 2000) return 0;
        G_ = n * n * n;
        gt = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
        if (!gt) return 0;
        for (int x = 0; x < G_; x++) {
            int a = x / (n * n), b = (x / n) % n, c = x % n;
            for (int y = 0; y < G_; y++) {
                int a2 = y / (n * n), b2 = (y / n) % n, c2 = y % n;
                int A = (a + a2) % n;
                int B = (b + b2) % n;
                int C = (c + c2 + a * b2) % n;
                gt[(size_t)x * G_ + y] = (A * n + B) * n + C;
            }
        }
        return 1;
    }
    return 0;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int t = perm[l * k + i], s = vol[l * k + i];
            for (int x = 0; x < G; x++) {
                int y = gt[(size_t)x * G + s];
                int a = i * G + x, b = (k + t) * G + y;
                nbr[(size_t)a * d + l] = b;
                nbr[(size_t)b * d + l] = a;
            }
        }
}

static long long eval_cost(void) {
    int k = k_, d = d_, N = N_;
    long long dups = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1 * k + i] == perm[l2 * k + i] && vol[l1 * k + i] == vol[l2 * k + i])
                    dups++;
    build_nbr();
    long long cost = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G_;
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
    if (argc < 10) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    int type = atoi(argv[6]);
    int gp1 = atoi(argv[7]), gp2 = atoi(argv[8]), gp3 = atoi(argv[9]);
    if (d_ < 1 || d_ > 64 || D_ < 1 || k_ < 1 || k_ > 16) { printf("0 0\n"); return 0; }
    if (!build_group(type, gp1, gp2, gp3)) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    if (N_ > 200000) { printf("0 0\n"); return 0; }

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

    long long cost = eval_cost();
    const double T0 = 6.0, T1 = 0.15;
    const int NCYC = 4;
    clock_t c0 = clock();
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double ph = el / limit * NCYC;
        ph -= floor(ph);
        double T = T0 * pow(T1 / T0, ph);

        int l = rint_(d_), i = rint_(k_);
        if (k_ >= 2 && rint_(3) == 0) {
            int i2 = rint_(k_ - 1);
            if (i2 >= i) i2++;
            int *pa = &perm[l * k_ + i], *pb = &perm[l * k_ + i2];
            int tmp = *pa; *pa = *pb; *pb = tmp;
            long long nc = eval_cost();
            long long delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                tmp = *pa; *pa = *pb; *pb = tmp;
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

    build_nbr();
    if (cost != 0) { printf("0 0\n"); return 0; }

    long long *pairs = malloc(sizeof(long long) * (size_t)N_ * d_);
    if (!pairs) { printf("0 0\n"); return 0; }
    int cnt = 0;
    for (int v = 0; v < N_; v++)
        for (int l = 0; l < d_; l++) {
            int u = nbr[(size_t)v * d_ + l];
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
# C engine 2: bipartite edge-toggle annealer with vertex growth, started from
# a valid graph. Each accepted zero-cost graph is saved and grown by a pair.
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
static int *deg, *adj, *side, *bestEu, *bestEv, *defl;
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
    defl = malloc(sizeof(int) * (size_t)cap_n);
    bufA = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    bufB = malloc(sizeof(u64) * (size_t)cap_n * cap_w);
    if (!deg || !side || !adj || !bestEu || !bestEv || !defl || !bufA || !bufB) {
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

        int ndef = 0;
        for (int v = 0; v < N; v++) if (deg[v] < d_) defl[ndef++] = v;

        int a = -1, b = -1;
        for (int t = 0; t < 50; t++) {
            int x = (ndef > 0 && rint_(2) == 0) ? defl[rint_(ndef)] : rint_(N);
            int y = (ndef > 0 && rint_(2) == 0) ? defl[rint_(ndef)] : rint_(N);
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

_KS = (1, 2, 3, 4, 5, 6)
_GMAX = 2000


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (type, p1, p2, p3, order) for a group of order >= target, or None.

    Mixes metacyclic groups Z_m x| Z_k2 and Heisenberg groups over Z_n (order n^3).
    """
    for _ in range(300):
        if rng.random() < 0.4:
            n = 2
            while n ** 3 < target:
                n += 1
            n += rng.choice((0, 0, 1))
            G = n ** 3
            if G > _GMAX:
                continue
            return (1, n, 0, 0, G)
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 16])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(80):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        G = m * k2
        if G > _GMAX:
            continue
        return (0, m, k2, r, G)
    return None


def _pick_k(rng, stats):
    """Bandit choice of base-block count k (mostly exploit, sometimes explore)."""
    if rng.random() < 0.25:
        return rng.choice(_KS)
    return max(_KS, key=lambda k: (stats[k][1] + 1) / (stats[k][0] + 2) + 0.02 * rng.random())


def _lift_in_c(d, D, k, typ, p1, p2, p3, seconds, seed):
    """Run the C lift annealer for one group; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_LIFT, [d, D, seed, f"{seconds:.2f}", k, typ, p1, p2, p3],
                    stdin_graph=None, timeout=seconds + 10.0)
    return lib.parse_graph_text(out)


def _grow_in_c(n, edges, d, D, seconds, seed, grow_max):
    """Run the C toggle annealer from a valid graph; returns parsed output (may be (0, []))."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", grow_max],
                    stdin_graph=(n, edges), timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.0, 0.85 * float(time_limit) - 1.5)
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    pg = None
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            if pg is not None and lib.is_prime_power(d - 1):
                return best  # exact extremal construction, nothing to search
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                try:
                    consider(*lib.araujo_lopez_graph(d - 2))
                except Exception:
                    pass

    try:
        # Phase 1: group-lift annealing over metacyclic and Heisenberg groups.
        lift_end = t0 + budget * 0.80
        stats = {k: [0, 0] for k in _KS}
        frac = 0.10
        misses = 0
        while True:
            remaining = lift_end - time.monotonic()
            if remaining < 1.0 or misses > 20:
                break
            k = _pick_k(rng, stats)
            target_n = int(best[0] * (1.0 + frac)) + 2
            g = _sample_group(max(2, -(-target_n // (2 * k))), rng)
            if g is None:
                misses += 1
                continue
            typ, p1, p2, p3, G = g
            if 2 * k * G <= best[0]:
                misses += 1
                continue
            misses = 0
            stats[k][0] += 1
            slice_s = min(remaining, min(6.0, max(1.5, 0.15 * remaining)))
            try:
                n_, e_ = _lift_in_c(d, D, k, typ, p1, p2, p3, slice_s,
                                    rng.randrange(1, 1 << 30))
            except RuntimeError:
                n_, e_ = 0, []
            if n_ > best[0] and lib.is_valid(n_, e_, d, D):
                stats[k][1] += 1
                best = (n_, e_)
                frac = min(0.20, frac * 1.3)
            else:
                frac = max(0.002, frac * 0.85)

        # Phase 2: grow the best valid graph by vertex pairs.
        c_budget = deadline - time.monotonic()
        if c_budget >= 1.5:
            try:
                cn, ce = _grow_in_c(best[0], best[1], d, D, c_budget,
                                    rng.randrange(1, 1 << 30), 200)
                consider(cn, ce)
            except Exception:
                pass  # keep the valid fallback
    except Exception:
        pass  # any search failure falls back to the valid graph already held

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if D == 1:
            best = (2, [(0, 1)])
    return best
