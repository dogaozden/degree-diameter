import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over Z_m x| Z_k2 (semidirect product).
#
# A candidate is a lift of a bipartite base graph with K vertices per side.
# Vertices are (A, i, g) and (B, j, h) with g, h in G = Z_m x| Z_k2. Each layer
# l gives a bijection i -> j = L[l][i] and a voltage s = S[l][i]. The edges are
# A(i, g) -- B(j, g*s). Every vertex has degree d, and the group acts regularly
# on each block, so the search only needs the exact count of pairs at distance
# greater than D (bitset ball expansion). Cost 0 means a valid graph. Moves are
# voltage changes aimed at blocks with unreached pairs, plus layer swaps. The
# C program stops at the first valid lift it finds and prints it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
typedef long long ll;

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K_, M_, K2_, R_, G_, N_, W_;
static int *pw, *S, *L, *IL, *nbr;
static u64 *bufA, *bufB;
static ll PEN;

/* group element x = a*K2 + b, (a,b)*(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a = x / K2_, b = x % K2_, c = y / K2_, e = y % K2_;
    int aa = (int)(((ll)a + (ll)pw[b] * c) % M_);
    int bb = (b + e) % K2_;
    return aa * K2_ + bb;
}

static int ginv(int x) {
    int a = x / K2_, b = x % K2_;
    int nb = (K2_ - b) % K2_;
    int aa = (int)((M_ - ((ll)pw[nb] * a) % M_) % M_);
    return aa * K2_ + nb;
}

static void build_nbr(void) {
    int K = K_, G = G_, d = d_;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = L[l * K + i];
                nbr[(size_t)v * d + l] = (K + j) * G + gmul(g, S[l * K + i]);
            }
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < G; h++) {
            int v = (K + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = IL[l * K + j];
                nbr[(size_t)v * d + l] = i * G + gmul(h, ginv(S[l * K + i]));
            }
        }
}

/* Returns cost = ordered pairs at distance > D_, plus a big penalty per duplicate edge.
   out_blk[b] receives the unreached count of block b (equal for all vertices in a block). */
static ll evaluate(int *out_blk) {
    int K = K_, G = G_, d = d_, N = N_, W = W_;
    ll dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (L[l * K + i] == L[l2 * K + i] && S[l * K + i] == S[l2 * K + i]) dup++;
    build_nbr();

    u64 *cur = bufA, *alt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 *x = alt + (size_t)v * W;
            const u64 *r = cur + (size_t)v * W;
            memcpy(x, r, sizeof(u64) * (size_t)W);
            const int *nb = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                const u64 *q = cur + (size_t)nb[l] * W;
                for (int w = 0; w < W; w++) x[w] |= q[w];
            }
            for (int w = 0; w < W; w++) {
                if (x[w] != r[w]) { changed = 1; break; }
            }
        }
        u64 *t = cur; cur = alt; alt = t;
        if (!changed) break;
    }

    ll cost = 0;
    for (int x = 0; x < 2 * K; x++) out_blk[x] = 0;
    for (int v = 0; v < N; v++) {
        const u64 *r = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += __builtin_popcountll(r[w]);
        int bad = N - cnt;
        cost += bad;
        out_blk[v / G] = bad;
    }
    (void)G;
    return cost + dup * PEN;
}

static void random_state(void) {
    int K = K_, d = d_, G = G_;
    for (int l = 0; l < d; l++) {
        int *p = L + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) IL[l * K + p[i]] = i;
    }
    for (int x = 0; x < d * K; x++) S[x] = rint_(G);
}

/* Swap the targets of A-vertices i1 and i2 in layer l. Applying it twice undoes it. */
static void swap_layer(int l, int i1, int i2) {
    int K = K_;
    int j1 = L[l * K + i1], j2 = L[l * K + i2];
    L[l * K + i1] = j2;
    L[l * K + i2] = j1;
    IL[l * K + j2] = i1;
    IL[l * K + j1] = i2;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    M_ = atoi(argv[6]);
    K2_ = atoi(argv[7]);
    R_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || K_ < 1 || M_ < 1 || K2_ < 1) { printf("0 0\n"); return 0; }
    G_ = M_ * K2_;
    N_ = 2 * K_ * G_;
    if (G_ < 2 || N_ > 6000) { printf("0 0\n"); return 0; }
    W_ = (N_ + 63) / 64;
    PEN = 4LL * N_ * N_;

    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (!rs) rs = 1;
    for (int t = 0; t < 20; t++) rnd();

    pw = malloc(sizeof(int) * (size_t)K2_);
    S = malloc(sizeof(int) * (size_t)d_ * K_);
    L = malloc(sizeof(int) * (size_t)d_ * K_);
    IL = malloc(sizeof(int) * (size_t)d_ * K_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    bufA = malloc(sizeof(u64) * (size_t)N_ * W_);
    bufB = malloc(sizeof(u64) * (size_t)N_ * W_);
    int *blk = malloc(sizeof(int) * (size_t)2 * K_);
    int *cblk = malloc(sizeof(int) * (size_t)2 * K_);
    if (!pw || !S || !L || !IL || !nbr || !bufA || !bufB || !blk || !cblk) {
        printf("0 0\n");
        return 0;
    }
    pw[0] = 1 % M_;
    for (int b = 1; b < K2_; b++) pw[b] = (int)(((ll)pw[b - 1] * R_) % M_);

    clock_t c0 = clock();
    random_state();
    ll cost = evaluate(blk);
    double T0 = 2.0 + 0.02 * (double)cost;
    const double T1 = 0.5;

    while (cost != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        if (K_ >= 2 && rint_(5) == 0) {
            int l = rint_(d_);
            int i1 = rint_(K_);
            int i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            swap_layer(l, i1, i2);
            ll nc = evaluate(cblk);
            ll delta = nc - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = nc;
                memcpy(blk, cblk, sizeof(int) * (size_t)2 * K_);
            } else {
                swap_layer(l, i1, i2);
            }
            continue;
        }

        int nbad = 0;
        for (int x = 0; x < 2 * K_; x++) if (blk[x] > 0) nbad++;
        int bx;
        if (nbad > 0 && rint_(10) < 7) {
            int pick = rint_(nbad);
            bx = -1;
            for (int y = 0; y < 2 * K_; y++) {
                if (blk[y] > 0) {
                    if (pick == 0) { bx = y; break; }
                    pick--;
                }
            }
        } else {
            bx = rint_(2 * K_);
        }
        int l = rint_(d_);
        int i = (bx < K_) ? bx : IL[l * K_ + (bx - K_)];
        int idx = l * K_ + i;
        int old = S[idx];
        int nw = rint_(G_);
        if (nw == old) continue;
        S[idx] = nw;
        ll nc = evaluate(cblk);
        ll delta = nc - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cost = nc;
            memcpy(blk, cblk, sizeof(int) * (size_t)2 * K_);
        } else {
            S[idx] = old;
        }
    }

    if (cost == 0) {
        build_nbr();
        int KG = K_ * G_;
        printf("%d %d\n", N_, KG * d_);
        for (int v = 0; v < KG; v++)
            for (int l = 0; l < d_; l++)
                printf("%d %d\n", v, nbr[(size_t)v * d_ + l]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)
_SLICE_MAX = 8.0


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (m, k2, r) with m * k2 = G and r^k2 = 1 mod m, or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            return m, 1, 1
        tries = [m - 1] if k2 == 2 else []
        tries += [rng.randrange(1, m) for _ in range(200)]
        tries.append(1)
        for r in tries:
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for this calibration case
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Bi-Cayley lift search: aim for groups whose lift is larger than the current best.
    end = t0 + max(0.0, 0.84 * time_limit - 4.0)
    slice_max = max(2.0, min(_SLICE_MAX, 0.18 * time_limit))
    while True:
        remain = end - time.monotonic()
        if remain < 2.5:
            break
        k = rng.choice(_KS)
        G = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
        g = None
        for _ in range(30):
            g = _sample_group(G, rng)
            if g is not None:
                break
            G += 1
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * G <= best[0]:
            continue
        budget = min(slice_max, remain - 1.0)
        if budget < 1.0:
            break
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 15.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
