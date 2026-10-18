import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of a bi-Cayley base graph.
#
# Group G = Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e)), r^k2 = 1 mod m.
# Base graph: K blocks on side A and K blocks on side B, each block a copy of G.
# Each layer l is a permutation P[l][.] of the K blocks, with voltage S[l][i]:
#     A(i,g) ~ B(P[l][i], g*S[l][i]).
# Every vertex gets exactly d neighbours (one per layer), and left multiplication
# by G is an automorphism, so the number of vertices at distance > D from every
# vertex of a block is the same. Cost therefore needs only one BFS per block
# (2K BFS runs instead of N), which makes each move cheap.
# cost = sum over block representatives of unreached vertices + PEN * duplicate darts.
# A valid lift has cost 0; the first one found is printed and the run stops.
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

static int d_, D_, K_, G_, m_, k2_;
static const long long PEN_ = 30;
static int *rpw;          /* rpw[b] = r^b mod m */
static int *P, *S;        /* index l*K_+i: target block and voltage */
static int *nbr;          /* nbr[v*d_+l] */
static int *seen, *qu;
static int gen_ = 0;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_;
    int c = y / k2_, e = y % k2_;
    int aa = (int)(((long long)a + (long long)rpw[b] * c) % m_);
    int bb = (b + e) % k2_;
    return aa * k2_ + bb;
}

static void build_layer(int l) {
    int dd = d_;
    for (int i = 0; i < K_; i++) {
        int j = P[l * K_ + i], s = S[l * K_ + i];
        for (int g = 0; g < G_; g++) {
            int A = i * G_ + g;
            int B = (K_ + j) * G_ + gmul(g, s);
            nbr[A * dd + l] = B;
            nbr[B * dd + l] = A;
        }
    }
}

static int dupcount(void) {
    int c = 0;
    int n = d_ * K_;
    for (int a = 0; a < n; a++) {
        int ia = a % K_;
        int ja = P[a], sa = S[a];
        for (int b = a + 1; b < n; b++) {
            if (b % K_ != ia) continue;
            if (P[b] == ja && S[b] == sa) c++;
        }
    }
    return c;
}

/* Sum over the 2K block representatives of the number of unreached vertices. */
static long long cost_fn(void) {
    int N2 = 2 * K_ * G_;
    int dd = d_;
    long long total = 0;
    for (int sb = 0; sb < 2 * K_; sb++) {
        int src = sb * G_;
        if (++gen_ == 0x7fffffff) { memset(seen, 0, sizeof(int) * (size_t)N2); gen_ = 1; }
        int head = 0, tail = 1;
        qu[0] = src;
        seen[src] = gen_;
        for (int dep = 0; dep < D_ && head < tail; dep++) {
            int lend = tail;
            while (head < lend) {
                int v = qu[head++];
                const int *nv = nbr + v * dd;
                for (int t = 0; t < dd; t++) {
                    int u = nv[t];
                    if (seen[u] != gen_) { seen[u] = gen_; qu[tail++] = u; }
                }
            }
        }
        total += N2 - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    K_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    int r = argc > 8 ? atoi(argv[8]) : 1;
    if (d_ < 1 || d_ > 64 || D_ < 1 || K_ < 1 || K_ > 64 || m_ < 1 || k2_ < 1 || k2_ > 64) {
        printf("0 0\n");
        return 0;
    }
    long long Gll = (long long)m_ * k2_;
    if (Gll * K_ * 2 > 400000) { printf("0 0\n"); return 0; }
    G_ = (int)Gll;

    rpw = malloc(sizeof(int) * (size_t)k2_);
    rpw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) rpw[b] = (int)((long long)rpw[b - 1] * (r % m_) % m_);
    if (((long long)rpw[k2_ - 1] * (r % m_)) % m_ != 1 % m_) {
        printf("0 0\n");   /* r^k2 != 1 mod m: not a group */
        return 0;
    }

    int nd = d_ * K_;
    int N2 = 2 * K_ * G_;
    P = malloc(sizeof(int) * (size_t)nd);
    S = malloc(sizeof(int) * (size_t)nd);
    nbr = malloc(sizeof(int) * (size_t)N2 * d_);
    seen = calloc((size_t)N2, sizeof(int));
    qu = malloc(sizeof(int) * (size_t)N2);
    if (!P || !S || !nbr || !seen || !qu) { printf("0 0\n"); return 0; }

    for (int l = 0; l < d_; l++) {
        int *p = P + l * K_;
        for (int i = 0; i < K_; i++) p[i] = i;
        for (int i = K_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K_; i++) S[l * K_ + i] = rint_(G_);
    }
    for (int l = 0; l < d_; l++) build_layer(l);

    long long cost = cost_fn() + PEN_ * dupcount();
    int found = (cost == 0);

    const double T0 = 8.0, T1 = 0.15, period = 3.0;
    double T = T0;
    clock_t c0 = clock();
    double el = 0.0;
    long long it = 0;
    while (!found) {
        if ((it & 63) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double frac = fmod(el, period) / period;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        int l = rint_(d_);
        if (K_ >= 2 && rdbl() < 0.2) {
            int *p = P + l * K_;
            int i1 = rint_(K_), i2 = rint_(K_ - 1);
            if (i2 >= i1) i2++;
            int tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
            build_layer(l);
            long long nc = cost_fn() + PEN_ * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = p[i1]; p[i1] = p[i2]; p[i2] = tmp;
                build_layer(l);
            }
        } else {
            int i = rint_(K_);
            int idx = l * K_ + i;
            int old = S[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            S[idx] = nw;
            build_layer(l);
            long long nc = cost_fn() + PEN_ * dupcount();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[idx] = old;
                build_layer(l);
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) { printf("0 0\n"); return 0; }
    int A = K_ * G_;
    printf("%d %d\n", N2, A * d_);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_SLICE = 4.0                      # seconds per C run (one group configuration)
_KS = (1, 2, 3, 4, 5, 6, 8, 9, 10, 12)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(G, rng):
    """Return (m, k2, r) with m*k2 = G describing Z_m x| Z_k2 (r^k2 = 1 mod m), or None."""
    if G < 2:
        return None
    divs = [k2 for k2 in range(2, min(G, 48) + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    order = ([1] + divs) if rng.random() < 0.15 else (divs + [1])
    for k2 in order:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        for _ in range(300):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
        return m, k2, 1           # abelian Z_m x Z_k2 is always a valid group
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))   # K_{d,d}, valid for D >= 2

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

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    # Ladder: each C run asks for a lift of order strictly above the current best.
    search_end = t0 + max(1.0, time_limit - 5.0)
    while True:
        remaining = search_end - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(_SLICE, remaining)

        k = pick_k()
        half = best[0] // 2
        step = max(1, half // 150)
        H_need = half + 1 + rng.randrange(0, step + 1)
        G_need = -(-H_need // k)
        grp = _sample_group(G_need, rng)
        if grp is None:
            continue
        m, k2, r = grp

        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{slice_s:.2f}", k, m, k2, r],
                            timeout=slice_s + 20.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > 0 and n > best[0]:
            before = best[0]
            consider(n, e)
            if best[0] > before:
                wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
