import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts (voltage graphs) over the
# semidirect product Z_m x| Z_k2 with k blocks per side. The lift is d-regular
# with 2*k*G vertices. Cost counts (vertex, target) pairs at distance > D from
# the 2k block representatives (group invariance covers all pairs), plus a
# penalty for duplicate darts. Cost zero means a valid graph, which is printed.
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

#define PEN 1000LL

static int d_, D_, k_, G_;
static int *mul_, *inv_, *tgt_, *itgt_, *vol_, *seen_, *queue_;
static int stamp_ = 0;

/* Neighbour of vertex v in layer l.
   A vertex (i,x) has index i*G+x; B vertex (j,y) has index k*G + j*G + y.
   Layer l joins A(i,x) to B(tgt[l][i], x*vol[l][i]). */
static inline int nb(int v, int l) {
    int k = k_, G = G_;
    if (v < k * G) {
        int i = v / G, x = v - i * G;
        int j = tgt_[l * k + i];
        int s = vol_[l * k + i];
        return k * G + j * G + mul_[x * G + s];
    } else {
        int w = v - k * G;
        int j = w / G, y = w - j * G;
        int i = itgt_[l * k + j];
        int s = vol_[l * k + i];
        return i * G + mul_[y * G + inv_[s]];
    }
}

static long long cost_of(void) {
    int k = k_, G = G_, d = d_, D = D_;
    int N = 2 * k * G;
    long long cost = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (tgt_[l1 * k + i] == tgt_[l2 * k + i] && vol_[l1 * k + i] == vol_[l2 * k + i])
                    cost += PEN;
    for (int r = 0; r < 2 * k; r++) {
        int src = (r < k) ? r * G : k * G + (r - k) * G;
        stamp_++;
        int head = 0, tail = 0;
        queue_[tail++] = src;
        seen_[src] = stamp_;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int v = queue_[head++];
                for (int l = 0; l < d; l++) {
                    int u = nb(v, l);
                    if (seen_[u] != stamp_) { seen_[u] = stamp_; queue_[tail++] = u; }
                }
            }
        }
        cost += N - tail;
    }
    return cost;
}

static void swap_tgt(int l, int i1, int i2) {
    int k = k_;
    int j1 = tgt_[l * k + i1], j2 = tgt_[l * k + i2];
    tgt_[l * k + i1] = j2;
    tgt_[l * k + i2] = j1;
    itgt_[l * k + j2] = i1;
    itgt_[l * k + j1] = i2;
}

static void random_state(void) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int p[64];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k; i++) {
            tgt_[l * k + i] = p[i];
            itgt_[l * k + p[i]] = i;
        }
        for (int i = 0; i < k; i++) vol_[l * k + i] = rint_(G);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    int k = atoi(argv[5]), m = atoi(argv[6]), k2 = atoi(argv[7]), r = atoi(argv[8]);
    d_ = d; D_ = D; k_ = k;
    if (d < 1 || D < 1 || k < 1 || k > 16 || m < 2 || k2 < 1 || r < 1 || r >= m) {
        printf("0 0\n");
        return 0;
    }
    long long Gll = (long long)m * k2;
    if (Gll < d || Gll > 2200) { printf("0 0\n"); return 0; }
    int G = (int)Gll;
    G_ = G;
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;

    int *pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)(((long long)pw[b - 1] * r) % m);
    if ((((long long)pw[k2 - 1]) * r) % m != 1 % m) { printf("0 0\n"); return 0; }

    mul_ = malloc(sizeof(int) * (size_t)G * (size_t)G);
    inv_ = malloc(sizeof(int) * (size_t)G);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, e = y % k2;
            int na = (int)(((long long)a + (long long)pw[b] * c) % m);
            int ne = (b + e) % k2;
            mul_[x * G + y] = na * k2 + ne;
        }
    }
    for (int x = 0; x < G; x++) inv_[x] = -1;
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            if (mul_[x * G + y] == 0) inv_[x] = y;
    for (int x = 0; x < G; x++) if (inv_[x] < 0) { printf("0 0\n"); return 0; }

    int N = 2 * k * G;
    tgt_ = malloc(sizeof(int) * (size_t)d * k);
    itgt_ = malloc(sizeof(int) * (size_t)d * k);
    vol_ = malloc(sizeof(int) * (size_t)d * k);
    seen_ = calloc((size_t)N, sizeof(int));
    queue_ = malloc(sizeof(int) * (size_t)N);

    random_state();
    long long cost = cost_of();
    clock_t c0 = clock();
    const double T0 = 40.0, T1 = 0.5;
    const long CYC = 20000;
    long it = 0;
    int ok = 0;

    while (1) {
        if (cost == 0) { ok = 1; break; }
        if ((it & 31) == 0 && (double)(clock() - c0) / CLOCKS_PER_SEC >= limit) break;
        long ph = it % CYC;
        double T = T0 * pow(T1 / T0, (double)ph / (double)CYC);
        it++;
        int l = rint_(d), i = rint_(k);
        if (k >= 2 && rdbl() < 0.3) {
            int i2 = rint_(k - 1);
            if (i2 >= i) i2++;
            swap_tgt(l, i, i2);
            long long nc = cost_of();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else swap_tgt(l, i, i2);
        } else {
            int old = vol_[l * k + i];
            int nv = rint_(G);
            if (nv == old) continue;
            vol_[l * k + i] = nv;
            long long nc = cost_of();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else vol_[l * k + i] = old;
        }
    }

    if (!ok) { printf("0 0\n"); return 0; }
    printf("%d %d\n", N, k * G * d);
    for (int v = 0; v < k * G; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb(v, l));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 1, 2, 2, 3, 4)
_GMAX = 2200
_SLICE = 7.0
_MARGIN = 4.0


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for degree d when d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


def _sample_group(lo, hi, rng):
    """Random (m, k2, r) with Z_m x| Z_k2 of order m*k2 in [lo, hi], or None."""
    for _ in range(300):
        k2 = rng.choice([1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 10, 12])
        mlo = max(2, -(-lo // k2))
        mhi = hi // k2
        if mhi < mlo:
            continue
        m = rng.randint(mlo, mhi)
        if k2 == 1:
            return m, 1, 1
        for _ in range(100):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _run_lift_search(d, D, k, m, k2, r, seconds, seed):
    """Run the C annealer on one group lift; returns (n, edges) or (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: Moore-optimal for d = 2
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}

    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for the D = 3 calibration case: return immediately.
    pg = _pg_fallback(d)
    if pg is not None:
        consider(pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best
    try:
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    except Exception:
        pass

    # Main search: bi-Cayley lifts over semidirect products, aiming slightly
    # above the current best order. The aim adapts: it grows after success
    # and shrinks after failure, so a weak start still reaches a valid graph.
    deadline = t0 + max(1.0, time_limit - _MARGIN)
    step = 0.06
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 2.0:
            break
        slice_s = min(_SLICE, remaining - 1.0)
        n_t = int(best[0] * (1.0 + step)) + 1
        k = rng.choice(_KS)
        lo = max(d, -(-n_t // (2 * k)))
        if lo > _GMAX:
            break
        hi = min(_GMAX, lo + max(2, lo // 60))
        g = _sample_group(lo, hi, rng)
        if g is None:
            continue
        m, k2, r = g
        before = best[0]
        try:
            n, e = _run_lift_search(d, D, k, m, k2, r, slice_s,
                                    rng.randrange(1, 1 << 30))
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback
        if best[0] > before:
            step = min(0.15, step * 1.3)
        else:
            step = max(0.003, step * 0.7)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
