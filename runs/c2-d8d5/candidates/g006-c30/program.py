import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts of bipartite base graphs over semidirect products
# Z_M x| Z_K2 (K blocks per side, d layers of permutations with voltages).
#
# Vertex (block b, element x) is coded b*G + x. A-blocks 0..K-1 and B-blocks
# K..2K-1. Layer l sends A-block i to B-block perm[l][i] with voltage volt[l][i]:
# (i, x) ~ (K + perm, x * volt). The group acts on the left by automorphisms, so
# the diameter condition only needs BFS from the 2K block representatives (b, 1).
# Cost = total unreached pairs over those BFS runs + penalty for duplicate darts.
# Moves: change a voltage, or swap the targets of two A-blocks in one layer.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
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

static int d_, D_, K_, G_, M_, K2_, R_, N_;
static int *mulT, *invT, *pw;
static int *perm, *pinv, *volt;
static int *dist, *queue;

static void build_group(void) {
    pw = malloc(sizeof(int) * (size_t)K2_);
    pw[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw[b] = (int)((long long)pw[b - 1] * R_ % M_);
    mulT = malloc(sizeof(int) * (size_t)G_ * (size_t)G_);
    invT = malloc(sizeof(int) * (size_t)G_);
    for (int x = 0; x < G_; x++) {
        int a = x / K2_, b = x % K2_;
        for (int y = 0; y < G_; y++) {
            int c = y / K2_, e = y % K2_;
            int ra = (int)((a + (long long)pw[b] * c) % M_);
            int rb = (b + e) % K2_;
            mulT[(size_t)x * G_ + y] = ra * K2_ + rb;
        }
    }
    for (int x = 0; x < G_; x++) {
        invT[x] = 0;
        for (int y = 0; y < G_; y++) {
            if (mulT[(size_t)x * G_ + y] == 0) { invT[x] = y; break; }
        }
    }
}

/* Number of vertices not within distance D_ of the source. */
static int bfs_unreached(int src) {
    int N = N_;
    for (int v = 0; v < N; v++) dist[v] = -1;
    int h = 0, t = 0, reached = 1;
    dist[src] = 0;
    queue[t++] = src;
    while (h < t) {
        int v = queue[h++];
        int dv = dist[v];
        if (dv >= D_) continue;
        int blk = v / G_, x = v % G_;
        if (blk < K_) {
            int i = blk;
            for (int l = 0; l < d_; l++) {
                int idx = l * K_ + i;
                int u = (K_ + perm[idx]) * G_ + mulT[(size_t)x * G_ + volt[idx]];
                if (dist[u] < 0) { dist[u] = dv + 1; queue[t++] = u; reached++; }
            }
        } else {
            int j = blk - K_;
            for (int l = 0; l < d_; l++) {
                int i = pinv[l * K_ + j];
                int idx = l * K_ + i;
                int u = i * G_ + mulT[(size_t)x * G_ + invT[volt[idx]]];
                if (dist[u] < 0) { dist[u] = dv + 1; queue[t++] = u; reached++; }
            }
        }
    }
    return N - reached;
}

static long long cost_fn(void) {
    long long c = 0;
    for (int u = 0; u < 2 * K_; u++) c += bfs_unreached(u * G_);
    long long dup = 0;
    for (int i = 0; i < K_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++) {
                int a = l * K_ + i, b = l2 * K_ + i;
                if (perm[a] == perm[b] && volt[a] == volt[b]) dup++;
            }
    return c + (long long)N_ * dup;
}

static int accept(long long delta, double T) {
    if (delta <= 0) return 1;
    return rdbl() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    K_ = atoi(argv[3]);
    M_ = atoi(argv[4]);
    K2_ = atoi(argv[5]);
    R_ = atoi(argv[6]);
    double limit = atof(argv[7]);
    rs ^= (uint64_t)strtoull(argv[8], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }
    G_ = M_ * K2_;
    N_ = 2 * K_ * G_;
    if (G_ > 2500 || N_ > 200000) { printf("0 0\n"); return 0; }

    build_group();
    perm = malloc(sizeof(int) * (size_t)K_ * d_);
    pinv = malloc(sizeof(int) * (size_t)K_ * d_);
    volt = malloc(sizeof(int) * (size_t)K_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    queue = malloc(sizeof(int) * (size_t)N_);

    for (int l = 0; l < d_; l++) {
        int *p = perm + l * K_;
        for (int i = 0; i < K_; i++) p[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K_; i++) pinv[l * K_ + p[i]] = i;
        for (int i = 0; i < K_; i++) volt[l * K_ + i] = rint_(G_);
    }

    const double T0 = 30.0, T1 = 0.3;
    clock_t c0 = clock();
    long long cost = cost_fn();

    while (cost != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        if (K_ >= 2 && rint_(2) == 1) {
            int l = rint_(d_);
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int a = l * K_ + i1, b = l * K_ + i2;
            int pa = perm[a], pb = perm[b];
            perm[a] = pb; perm[b] = pa;
            pinv[l * K_ + pb] = i1;
            pinv[l * K_ + pa] = i2;
            long long nc = cost_fn();
            if (accept(nc - cost, T)) {
                cost = nc;
            } else {
                perm[a] = pa; perm[b] = pb;
                pinv[l * K_ + pa] = i1;
                pinv[l * K_ + pb] = i2;
            }
        } else {
            int idx = rint_(d_ * K_);
            int old = volt[idx];
            int nv = rint_(G_);
            if (nv == old) continue;
            volt[idx] = nv;
            long long nc = cost_fn();
            if (accept(nc - cost, T)) cost = nc;
            else volt[idx] = old;
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }

    long long E = (long long)K_ * G_ * d_;
    printf("%d %lld\n", N_, E);
    for (int i = 0; i < K_; i++)
        for (int x = 0; x < G_; x++)
            for (int l = 0; l < d_; l++) {
                int idx = l * K_ + i;
                int u = i * G_ + x;
                int v = (K_ + perm[idx]) * G_ + mulT[(size_t)x * G_ + volt[idx]];
                printf("%d %d\n", u, v);
            }
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


def _group_options(G, rng):
    """Semidirect products Z_M x| Z_k2 of order G, as (M, k2, r) triples."""
    opts = []
    for k2 in range(1, min(G, 16) + 1):
        if G % k2:
            continue
        M = G // k2
        if M < 2:
            continue
        if k2 == 1:
            opts.append((M, 1, 1))
            continue
        rs = [r for r in range(1, M)
              if math.gcd(r, M) == 1 and pow(r, k2, M) == 1 % M]
        for r in rng.sample(rs, min(3, len(rs))):
            opts.append((M, k2, r))
    return opts


def _run_lift(d, D, K, M, k2, r, seconds, seed):
    """Run the C lift annealer; returns (n, edges) or (0, []) if it found nothing."""
    out = lib.run_c(C_SOURCE, [d, D, K, M, k2, r, f"{seconds:.2f}", seed],
                    stdin_graph=None, timeout=seconds + 15.0)
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

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass
        if pg is not None and lib.is_prime_power(d - 1):
            return best

    # Voltage-lift search over semidirect products. The target grows each time
    # a larger valid lift is found.
    deadline = t0 + max(1.0, time_limit - 10.0)
    K_LIST = [1, 2, 3, 4, 5, 6, 8]
    half = best[0] // 2 + 1  # need K * G >= half

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.8:
            break
        candidates = [K for K in K_LIST
                      if max(4, -(-half // K)) + 2 <= 2000]
        if not candidates:
            break
        K = rng.choice(candidates)
        Gmin = max(4, -(-half // K))
        G = Gmin + rng.randrange(0, 3)
        opts = _group_options(G, rng)
        if not opts:
            continue
        M, k2, r = rng.choice(opts)
        secs = min(5.0, remaining)
        try:
            n, e = _run_lift(d, D, K, M, k2, r, secs, rng.randrange(1, 1 << 30))
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            half = best[0] // 2 + 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
