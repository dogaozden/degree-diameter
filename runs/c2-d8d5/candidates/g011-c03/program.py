import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts.
#
# A lift over the group G = Z_m x| Z_k2 (element a*k2+b, product
# (a,b)(c,e) = (a + r^b c, b+e)) has 2kG vertices: A-blocks i in 0..k-1 and
# B-blocks j in 0..k-1, each vertex (block, g). Each of the d layers l gives a
# permutation lay[l][i] (A-block i goes to B-block lay[l][i]) and a voltage
# sv[l][i]: (i,g) ~ (j, g*s). Every vertex gets exactly one neighbour per layer,
# so the degree is d.
#
# Left multiplication by G is an automorphism, so every block is vertex
# transitive. Diameter <= D therefore holds iff a BFS from each of the 2k
# block roots reaches all vertices within D steps. The cost is the total number
# of unreached (root, vertex) pairs plus a penalty per duplicate dart.
# Cost 0 means a valid graph, which is printed immediately.
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

#define PEN 40
#define RESTART 40000

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int pw[256];
static int *lay, *sv, *nb, *dist, *queue, *bl, *bs;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    long long aa = ((long long)a + (long long)pw[b] * c) % m_;
    return (int)(aa * k2_ + (b + e) % k2_);
}

static void randomize(void) {
    int tmp[64];
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) tmp[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = tmp[i]; tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k_; i++) lay[l * k_ + i] = tmp[i];
    }
    for (int x = 0; x < d_ * k_; x++) sv[x] = rint_(G_);
}

static void build_nb(void) {
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) {
            int j = lay[l * k_ + i], s = sv[l * k_ + i];
            for (int g = 0; g < G_; g++) {
                int u = i * G_ + g;
                int v = (k_ + j) * G_ + gmul(g, s);
                nb[u * d_ + l] = v;
                nb[v * d_ + l] = u;
            }
        }
    }
}

static long long eval_cost(void) {
    int N = N_;
    long long tot = 0;
    for (int rt = 0; rt < 2 * k_; rt++) {
        int root = rt * G_;
        for (int v = 0; v < N; v++) dist[v] = -1;
        int h = 0, t = 0;
        queue[t++] = root;
        dist[root] = 0;
        while (h < t) {
            int v = queue[h++];
            if (dist[v] >= D_) continue;
            for (int l = 0; l < d_; l++) {
                int u = nb[v * d_ + l];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; queue[t++] = u; }
            }
        }
        tot += N - t;
    }
    int nd = d_ * k_;
    for (int a = 0; a < nd; a++)
        for (int b = a + 1; b < nd; b++)
            if (a % k_ == b % k_ && lay[a] == lay[b] && sv[a] == sv[b]) tot += PEN;
    return tot;
}

static void print_graph(void) {
    int m = 0;
    for (int u = 0; u < N_; u++)
        for (int l = 0; l < d_; l++)
            if (nb[u * d_ + l] > u) m++;
    printf("%d %d\n", N_, m);
    for (int u = 0; u < N_; u++)
        for (int l = 0; l < d_; l++) {
            int v = nb[u * d_ + l];
            if (v > u) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    k_ = atoi(argv[3]);
    m_ = atoi(argv[4]);
    k2_ = atoi(argv[5]);
    r_ = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;
    if (d_ < 2 || D_ < 1 || k_ < 1 || k_ > 64 || m_ < 2 || k2_ < 1 || k2_ > 200 ||
        N_ > 200000) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++)
        pw[b] = (int)((long long)pw[b - 1] * (r_ % m_) % m_);

    int nd = d_ * k_;
    lay = malloc(sizeof(int) * nd);
    sv = malloc(sizeof(int) * nd);
    bl = malloc(sizeof(int) * nd);
    bs = malloc(sizeof(int) * nd);
    nb = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * N_);
    queue = malloc(sizeof(int) * N_);
    if (!lay || !sv || !bl || !bs || !nb || !dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    randomize();
    build_nb();
    long long cost = eval_cost();
    long long bestc = cost;
    int since = 0;
    clock_t c0 = clock();
    const double T0 = 6.0, T1 = 0.25;

    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(bl, lay, sizeof(int) * nd);
        memcpy(bs, sv, sizeof(int) * nd);
        if (k_ >= 2 && rint_(4) == 0) {
            int l = rint_(d_);
            int i1 = rint_(k_), i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            int t = lay[l * k_ + i1];
            lay[l * k_ + i1] = lay[l * k_ + i2];
            lay[l * k_ + i2] = t;
        } else {
            int idx = rint_(nd);
            sv[idx] = rint_(G_);
        }

        build_nb();
        long long nc = eval_cost();
        long long delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost < bestc) { bestc = cost; since = 0; }
            else since++;
        } else {
            memcpy(lay, bl, sizeof(int) * nd);
            memcpy(sv, bs, sizeof(int) * nd);
            build_nb();
            since++;
        }
        if (cost == 0) break;
        if (since > RESTART) {
            randomize();
            build_nb();
            cost = eval_cost();
            bestc = cost;
            since = 0;
        }
    }

    if (cost == 0) print_graph();
    else printf("0 0\n");
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


def _pick_group(G, rng):
    """Return (m, k2, r) with Z_m x| Z_k2 of order exactly G, or None."""
    k2s = [k for k in range(1, min(G, 64) + 1) if G % k == 0 and G // k >= 2]
    if not k2s:
        return None
    k2 = rng.choice(k2s)
    m = G // k2
    r = 1  # direct product: always a valid choice
    if k2 > 1 and rng.random() < 0.7:
        for _ in range(100):
            c = rng.randrange(2, m) if m > 2 else 1
            if c != 1 and math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])
        if D == 3 and lib.is_prime_power(d - 1):
            return best

    if d >= 2 and D >= 2:
        end = t0 + max(1.0, time_limit - 5.0)
        tries = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        errors = 0

        def pick_k():
            if rng.random() < 0.25:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (tries[k] + 2) + 0.05 * rng.random())

        while True:
            remaining = end - time.monotonic()
            if remaining < 2.0 or errors >= 3:
                break
            k = pick_k()
            tries[k] += 1
            # Aim just above the current best order: 2 * k * G > best.
            G = best[0] // (2 * k) + 1
            if rng.random() < 0.3:
                G += 1
            grp = _pick_group(G, rng)
            if grp is None:
                continue
            m, k2, r = grp
            slice_s = min(remaining - 1.0, 6.0 + 4.0 * rng.random())
            if slice_s < 1.0:
                break
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, k, m, k2, r, rng.randrange(1, 1 << 30), f"{slice_s:.2f}"],
                    timeout=slice_s + 15.0,
                )
                n, e = lib.parse_graph_text(out)
            except (RuntimeError, ValueError):
                errors += 1
                continue
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
                wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
