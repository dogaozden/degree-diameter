import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley lift annealer over Z_M x| Z_K2.
#
# The graph is a lift of a base with 2K blocks (K left, K right). Each block has
# G = M*K2 vertices, and the group acts by left multiplication, which is an
# automorphism. Layer l joins left block i to right block sig[l][i] with voltage
# volt[l][i]. The graph is d-regular as a multigraph; duplicates only lower the
# degree and do not change distances. Validity is checked from one representative
# per block (2K BFS runs), because the group action is transitive on each block.
# Cost = total unreached vertices over the representatives. Annealing moves change
# one voltage or swap two right-block assignments inside one layer. Exits as soon
# as cost is 0 and prints the lift.
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

static int d_, D_, K, M, K2, G, N, R;
static int *pw, *sig, *siginv, *volt, *nbr, *vis, *qbuf;
static int visstamp = 0;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

/* element code = a*K2 + b, (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ca = (int)(((long long)a + (long long)pw[b] * c) % M);
    int ce = (b + e) % K2;
    return ca * K2 + ce;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int ia = (int)((M - ((long long)pw[nb] * a) % M) % M);
    return ia * K2 + nb;
}

static void recompute_inv(int l) {
    for (int i = 0; i < K; i++) siginv[l * K + sig[l * K + i]] = i;
}

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = sig[l * K + i];
        int g = volt[l * K + i];
        for (int x = 0; x < G; x++)
            nbr[(i * G + x) * d_ + l] = (K + j) * G + gmul(x, g);
    }
    for (int j = 0; j < K; j++) {
        int i = siginv[l * K + j];
        int gi = ginv(volt[l * K + i]);
        for (int y = 0; y < G; y++)
            nbr[((K + j) * G + y) * d_ + l] = i * G + gmul(y, gi);
    }
}

/* number of vertices within distance D_ of s (including s) */
static int ball(int s) {
    visstamp++;
    int h = 0, t = 1, levelEnd = 1;
    qbuf[0] = s;
    vis[s] = visstamp;
    for (int depth = 0; depth < D_ && h < levelEnd; depth++) {
        while (h < levelEnd) {
            int v = qbuf[h++];
            const int *nb = nbr + v * d_;
            for (int l = 0; l < d_; l++) {
                int u = nb[l];
                if (vis[u] != visstamp) { vis[u] = visstamp; qbuf[t++] = u; }
            }
        }
        levelEnd = t;
    }
    return t;
}

static long long evalcost(void) {
    long long c = 0;
    for (int i = 0; i < 2 * K; i++) c += (long long)(N - ball(i * G));
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K < 1 || M < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    if ((long long)M * K2 > 20000 || 2LL * K * M * K2 > 20000) { printf("0 0\n"); return 0; }
    G = M * K2;
    N = 2 * K * G;

    int one = 1 % M;
    pw = malloc(sizeof(int) * K2);
    pw[0] = one;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * (R % M) % M);
    long long rk = (long long)pw[K2 - 1] * (R % M) % M;
    if (rk != one) { printf("0 0\n"); return 0; }
    if (M > 1 && gcd_(R % M, M) != 1) { printf("0 0\n"); return 0; }

    sig = malloc(sizeof(int) * d_ * K);
    siginv = malloc(sizeof(int) * d_ * K);
    volt = malloc(sizeof(int) * d_ * K);
    nbr = malloc(sizeof(int) * (size_t)N * d_);
    vis = calloc((size_t)N, sizeof(int));
    qbuf = malloc(sizeof(int) * (size_t)N);
    if (!sig || !siginv || !volt || !nbr || !vis || !qbuf) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) sig[l * K + i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * K + i]; sig[l * K + i] = sig[l * K + j]; sig[l * K + j] = t;
        }
        for (int i = 0; i < K; i++) volt[l * K + i] = rint_(G);
        recompute_inv(l);
        rebuild_layer(l);
    }

    long long cost = evalcost();
    int found = (cost == 0);
    double c0 = (double)cost;
    const double T0 = 1.0 + 0.02 * c0, T1 = 0.05;
    clock_t tc = clock();

    while (!found) {
        double el = (double)(clock() - tc) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (K >= 2 && rint_(10) < 3) {
            int l = rint_(d_);
            int i1 = rint_(K), i2 = rint_(K);
            if (i1 == i2) continue;
            int t = sig[l * K + i1]; sig[l * K + i1] = sig[l * K + i2]; sig[l * K + i2] = t;
            recompute_inv(l);
            rebuild_layer(l);
            long long c2 = evalcost();
            long long delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
                if (cost == 0) found = 1;
            } else {
                t = sig[l * K + i1]; sig[l * K + i1] = sig[l * K + i2]; sig[l * K + i2] = t;
                recompute_inv(l);
                rebuild_layer(l);
            }
        } else {
            int l = rint_(d_), i = rint_(K);
            int old = volt[l * K + i];
            int nw = rint_(G);
            if (nw == old) continue;
            volt[l * K + i] = nw;
            rebuild_layer(l);
            long long c2 = evalcost();
            long long delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
                if (cost == 0) found = 1;
            } else {
                volt[l * K + i] = old;
                rebuild_layer(l);
            }
        }
    }

    if (!found) { printf("0 0\n"); return 0; }

    int half = K * G;
    int *tmp = malloc(sizeof(int) * d_);
    long long cap = (long long)half * d_;
    int *eu = malloc(sizeof(int) * cap);
    int *ev = malloc(sizeof(int) * cap);
    if (!tmp || !eu || !ev) { printf("0 0\n"); return 0; }
    int m = 0;
    for (int v = 0; v < half; v++) {
        for (int l = 0; l < d_; l++) tmp[l] = nbr[v * d_ + l];
        for (int a = 1; a < d_; a++) {
            int x = tmp[a], b = a - 1;
            while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
            tmp[b + 1] = x;
        }
        for (int l = 0; l < d_; l++) {
            if (l == 0 || tmp[l] != tmp[l - 1]) {
                eu[m] = v;
                ev[m] = tmp[l];
                m++;
            }
        }
    }
    printf("%d %d\n", N, m);
    for (int e = 0; e < m; e++) printf("%d %d\n", eu[e], ev[e]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: vertex-growth annealer (edge toggling with bitset ball checks).
# Used as the final stage, starting from the best valid graph found so far.
# ----------------------------------------------------------------------------

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

_KS = (1, 2, 3, 4, 5, 6, 8)
_K2S = (1, 1, 2, 2, 3, 4, 5, 6, 8)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G_min, rng):
    """Return (M, K2, R) for Z_M x| Z_K2 with M*K2 >= G_min, near G_min."""
    K2 = rng.choice(_K2S)
    M = max(2, -(-G_min // K2)) + rng.randrange(0, 3)
    if K2 == 1:
        return M, 1, 1
    rs_ = [r for r in range(2, M) if math.gcd(r, M) == 1 and pow(r, K2, M) == 1]
    R = rng.choice(rs_) if rs_ and rng.random() < 0.8 else 1
    return M, K2, R


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: bi-Cayley lift search in C, growing the target order each success.
    lift_end = t0 + 0.70 * time_limit
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 3.0:
            break
        slice_s = min(max(3.0, remaining / 3.0), 8.0)
        k = rng.choice(_KS)
        G_min = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
        M, K2, R = _sample_group(G_min, rng)
        n_cand = 2 * k * M * K2
        if n_cand <= best[0] or n_cand > 20000:
            continue
        try:
            out = lib.run_c(C_LIFT, [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}",
                                     k, M, K2, R],
                            timeout=slice_s + 20.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass  # keep the valid fallback

    # Stage 2: vertex growth in C from the best valid graph.
    rem = t0 + 0.90 * time_limit - time.monotonic() - 2.0
    if rem >= 1.0:
        try:
            out = lib.run_c(C_GROW, [d, D, rng.randrange(1, 1 << 30), f"{rem:.2f}", 200],
                            stdin_graph=best, timeout=rem + 20.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
