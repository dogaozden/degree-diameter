import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/*
 * Bi-Cayley lift search over semidirect products Z_M x| Z_K2.
 *
 * Base: K blocks A_0..A_{K-1} and K blocks B_0..B_{K-1}, each block a copy of G.
 * Dart l sends A_i to B_{sig[l][i]} with voltage sv[l][i]:
 *     A_{i,g} ~ B_{sig[l][i], g*sv[l][i]}.
 * Each sig[l] is a permutation, so the lift is d-regular and bipartite.
 *
 * Left multiplication by a group element is an automorphism, so the ball of
 * every vertex is a translate of the ball of a block representative. We
 * therefore only track 2K bits per vertex (one per representative), which
 * costs O(D * N * d) per evaluation with one u64 OR per neighbour.
 *
 * Cost = number of (representative, vertex) pairs at distance > D, plus a
 * penalty for repeated (target, voltage) pairs at the same block. Cost 0
 * means a valid simple lift of order 2*K*G.
 *
 * Driver: targets a lift with K*G >= target. On success the target moves
 * just above the new size; after repeated failures the step size shrinks.
 */

typedef uint64_t u64;
typedef long long ll;

#define MAXK 32
#define MAXK2 64
#define PEN 10
#define ITER_CAP 20000
#define PATIENCE 5000

static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rnd_int(int n) { return (int)(rnd64() % (u64)n); }
static double rnd_dbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, K, M_, K2_, G;
static ll pw[MAXK2];

static int *sig, *isig, *sv, *isv;
static int *bak_sig, *bak_isig, *bak_sv, *bak_isv;
static int *nbr = NULL;
static u64 *rA = NULL, *rB = NULL;
static int cap_nv = 0;

static int best_NV = 0, best_m = 0, cap_best = 0;
static int *bestU = NULL, *bestV = NULL;

static clock_t c0;
static double limit_s;

static double elapsed(void) { return (double)(clock() - c0) / CLOCKS_PER_SEC; }

static int popc(u64 x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static ll gcd_ll(ll a, ll b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { ll t = a % b; a = b; b = t; }
    return a;
}

static ll powmod_ll(ll b, ll e, ll m) {
    ll r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product: element a*K2 + b means (a, b); (a,b)*(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2_, b = x - a * K2_;
    int c = y / K2_, e = y - c * K2_;
    ll t = ((ll)a + pw[b] * (ll)c) % M_;
    int ee = b + e;
    if (ee >= K2_) ee -= K2_;
    return (int)(t * K2_ + ee);
}

static int ginv(int x) {
    int a = x / K2_, b = x - a * K2_;
    int nb = (b == 0) ? 0 : K2_ - b;
    ll t = (-(pw[nb] * (ll)a)) % M_;
    if (t < 0) t += M_;
    return (int)(t * K2_ + nb);
}

static const int K2_CH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static void set_group(ll Gwant) {
    int k2 = K2_CH[rnd_int(20)];
    ll M = (Gwant + k2 - 1) / k2;
    if (M < 2) M = 2;
    ll r = 1;
    if (k2 > 1 && M > 2) {
        for (int t = 0; t < 2000; t++) {
            ll c = 2 + (ll)rnd_int((int)(M - 2));
            if (gcd_ll(c, M) != 1) continue;
            if (powmod_ll(c, k2, M) != 1 % M) continue;
            r = c;
            break;
        }
    }
    M_ = (int)M;
    K2_ = k2;
    G = (int)(M * k2);
    for (int b = 0; b < k2; b++) pw[b] = powmod_ll(r, b, M);
}

static void ensure_nv(int nv) {
    if (nv <= cap_nv) return;
    free(nbr); free(rA); free(rB);
    nbr = malloc(sizeof(int) * (size_t)nv * d_);
    rA = malloc(sizeof(u64) * (size_t)nv);
    rB = malloc(sizeof(u64) * (size_t)nv);
    if (!nbr || !rA || !rB) { printf("0 0\n"); exit(0); }
    cap_nv = nv;
}

static void init_random(void) {
    int perm[MAXK];
    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            sig[l * K + i] = perm[i];
            isig[l * K + perm[i]] = i;
            int s = rnd_int(G);
            sv[l * K + i] = s;
            isv[l * K + i] = ginv(s);
        }
    }
}

static ll evaluate(void) {
    const int KG = K * G, N = 2 * KG;
    for (int v = 0; v < KG; v++) {
        int i = v / G, g = v - i * G;
        int *nb = nbr + (size_t)v * d_;
        for (int l = 0; l < d_; l++) {
            int j = sig[l * K + i];
            nb[l] = (K + j) * G + gmul(g, sv[l * K + i]);
        }
    }
    for (int w = 0; w < KG; w++) {
        int j = w / G, h = w - j * G;
        int *nb = nbr + (size_t)(KG + w) * d_;
        for (int l = 0; l < d_; l++) {
            int i = isig[l * K + j];
            nb[l] = i * G + gmul(h, isv[l * K + i]);
        }
    }

    u64 *buf = rA, *alt = rB;
    for (int v = 0; v < N; v++) buf[v] = 0;
    for (int b = 0; b < 2 * K; b++) buf[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = buf[v];
            const int *nb = nbr + (size_t)v * d_;
            for (int l = 0; l < d_; l++) x |= buf[nb[l]];
            alt[v] = x;
            if (x != buf[v]) changed = 1;
        }
        u64 *tmp = buf; buf = alt; alt = tmp;
        if (!changed) break;
    }
    rA = buf;
    rB = alt;

    ll unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - popc(buf[v]);

    ll dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (sig[l * K + i] == sig[l2 * K + i] && sv[l * K + i] == sv[l2 * K + i]) dup++;

    return unr + PEN * dup;
}

static void save_best(void) {
    const int KG = K * G;
    int m = KG * d_;
    if (m > cap_best) {
        int *a = realloc(bestU, sizeof(int) * (size_t)m);
        int *b = realloc(bestV, sizeof(int) * (size_t)m);
        if (!a || !b) { printf("0 0\n"); exit(0); }
        bestU = a; bestV = b; cap_best = m;
    }
    int c = 0;
    for (int v = 0; v < KG; v++)
        for (int l = 0; l < d_; l++) {
            bestU[c] = v;
            bestV[c] = nbr[(size_t)v * d_ + l];
            c++;
        }
    best_NV = 2 * KG;
    best_m = c;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    limit_s = atof(argv[4]);
    ll min_kg = argc > 5 ? atoll(argv[5]) : 1;
    int kmax = argc > 6 ? atoi(argv[6]) : 6;
    if (kmax < 1) kmax = 1;
    if (kmax > MAXK) kmax = MAXK;
    if (d_ < 1 || d_ > 4096 || D_ < 2) { printf("0 0\n"); return 0; }
    if (min_kg < 1) min_kg = 1;

    size_t blk = sizeof(int) * (size_t)d_ * MAXK;
    sig = malloc(blk); isig = malloc(blk); sv = malloc(blk); isv = malloc(blk);
    bak_sig = malloc(blk); bak_isig = malloc(blk); bak_sv = malloc(blk); bak_isv = malloc(blk);
    if (!sig || !isig || !sv || !isv || !bak_sig || !bak_isig || !bak_sv || !bak_isv) {
        printf("0 0\n");
        return 0;
    }

    c0 = clock();
    ll last = min_kg - 1;
    if (last < 1) last = 1;
    ll step = last / 128;
    if (step < 1) step = 1;
    ll target = last + step;
    int fails = 0;

    while (elapsed() < limit_s) {
        K = 1 + rnd_int(kmax);
        ll Gmin = (target + K - 1) / K;
        if (Gmin < 2) Gmin = 2;
        set_group(Gmin + rnd_int((int)(Gmin / 64) + 2));
        ll KG = (ll)K * G;
        if (KG > 2000000) { target = last + step; continue; }
        ensure_nv((int)(2 * KG));
        init_random();

        ll cur = evaluate();
        double T0 = 1.0 + 0.1 * (double)cur;
        if (T0 > 200.0) T0 = 200.0;
        const double T1 = 0.3;
        ll best_c = cur;
        int last_imp = 0;

        for (int it = 0; it < ITER_CAP && cur > 0; it++) {
            if ((it & 63) == 0 && elapsed() >= limit_s) break;
            if (it - last_imp > PATIENCE) break;
            double T = T0 * pow(T1 / T0, (double)it / ITER_CAP);

            size_t nsz = sizeof(int) * (size_t)d_ * K;
            memcpy(bak_sig, sig, nsz);
            memcpy(bak_isig, isig, nsz);
            memcpy(bak_sv, sv, nsz);
            memcpy(bak_isv, isv, nsz);

            if (K >= 2 && rnd_dbl() < 0.3) {
                int l = rnd_int(d_);
                int i1 = rnd_int(K);
                int i2 = rnd_int(K - 1);
                if (i2 >= i1) i2++;
                int j1 = sig[l * K + i1], j2 = sig[l * K + i2];
                sig[l * K + i1] = j2;
                sig[l * K + i2] = j1;
                isig[l * K + j2] = i1;
                isig[l * K + j1] = i2;
            } else {
                int l = rnd_int(d_), i = rnd_int(K);
                int ns = rnd_int(G);
                if (ns == sv[l * K + i]) continue;
                sv[l * K + i] = ns;
                isv[l * K + i] = ginv(ns);
            }

            ll nc = evaluate();
            double delta = (double)(nc - cur);
            if (nc <= cur || rnd_dbl() < exp(-delta / T)) {
                cur = nc;
                if (cur < best_c) { best_c = cur; last_imp = it; }
            } else {
                memcpy(sig, bak_sig, nsz);
                memcpy(isig, bak_isig, nsz);
                memcpy(sv, bak_sv, nsz);
                memcpy(isv, bak_isv, nsz);
            }
        }

        if (cur == 0) {
            /* nbr holds the accepted state's adjacency. */
            save_best();
            last = KG;
            fails = 0;
            step = KG / 128;
            if (step < 1) step = 1;
            target = last + step;
        } else {
            if (++fails >= 25) {
                fails = 0;
                if (step > 1) step /= 2;
            }
            target = last + step;
        }
    }

    if (best_NV == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_NV, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _run_lift_search(d, D, min_kg, seconds, seed, kmax):
    """Run the C lift annealer; returns (n, edges), possibly (0, [])."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", int(min_kg), int(kmax)],
                    timeout=seconds + 15.0)
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
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact optimum for the calibration case
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Bi-Cayley lift search in C, targeting orders above the current best.
    budget = max(0.0, 0.8 * time_limit - 3.0)
    left = budget - (time.monotonic() - t0)
    if left >= 3.0:
        try:
            n2, e2 = _run_lift_search(d, D, best[0] // 2 + 1, left,
                                      rng.randrange(1, 1 << 30), 6)
            consider(n2, e2)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
