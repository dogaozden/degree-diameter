import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Lift search over semidirect products Z_m x| Z_k2 (order G = m*k2).
#
# The graph is a bipartite lift with 2k base vertices (k per side). Each left
# block i sends one dart per layer l to right block lay[l][i] with voltage
# vol[l][i] in G, so every vertex has degree d. Edges are (i,x)-(j, x*s), and
# left multiplication by G acts as automorphisms, so the graph is valid iff
# each identity vertex (block b, element 1) reaches every vertex within D.
# Reachability is a bitmask propagation over 2k bits per vertex, which is
# cheap enough for millions of evaluations. Simulated annealing moves
# voltages and layer permutations, with a penalty for parallel edges.
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

static int d_, D_, k_, m_, k2_, G_, N_;
static int *mulT, *invT, *pw, *lay, *vol, *nbr, *linv;
static u64 *cur, *nxt;

static int gmul(int x, int y) {
    int a = x / k2_, b = x % k2_, c = y / k2_, e = y % k2_;
    int ra = (a + pw[b] * c) % m_;
    int rb = (b + e) % k2_;
    return ra * k2_ + rb;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            linv[l * k + lay[l * k + i]] = i;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++) {
                int j = lay[l * k + i];
                nbr[v * d + l] = (k + j) * G + mulT[g * G + vol[l * k + i]];
            }
        }
    for (int j = 0; j < k; j++)
        for (int g = 0; g < G; g++) {
            int v = (k + j) * G + g;
            for (int l = 0; l < d; l++) {
                int i = linv[l * k + j];
                nbr[v * d + l] = i * G + mulT[g * G + invT[vol[l * k + i]]];
            }
        }
}

/* Returns 0 for a valid lift, otherwise a positive penalty-weighted cost. */
static long long evaluate(void) {
    int B = 2 * k_, N = N_, d = d_;
    build_nbr();
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < B; b++) cur[b * G_] = 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            const int *nb = nbr + v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long long un = 0;
    for (int v = 0; v < N; v++) un += B - __builtin_popcountll(cur[v]);
    long long dup = 0;
    for (int i = 0; i < k_; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1 * k_ + i] == lay[l2 * k_ + i] &&
                    vol[l1 * k_ + i] == vol[l2 * k_ + i])
                    dup++;
    return un + 40 * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    k_ = atoi(argv[3]);
    m_ = atoi(argv[4]);
    k2_ = atoi(argv[5]);
    int r = atoi(argv[6]);
    rs ^= (u64)strtoull(argv[7], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[8]);
    if (limit <= 0) limit = 1.0;
    if (d_ < 1 || D_ < 1 || k_ < 1 || 2 * k_ > 64 || m_ < 1 || k2_ < 1) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    if (G_ > 2000) { printf("0 0\n"); return 0; }
    N_ = 2 * k_ * G_;
    if (N_ > 200000) { printf("0 0\n"); return 0; }
    r %= m_;
    if (r < 0) r += m_;

    pw = malloc(sizeof(int) * k2_);
    pw[0] = 1 % m_;
    for (int b = 1; b < k2_; b++) pw[b] = (pw[b - 1] * r) % m_;

    mulT = malloc(sizeof(int) * (size_t)G_ * G_);
    invT = malloc(sizeof(int) * G_);
    lay = malloc(sizeof(int) * d_ * k_);
    vol = malloc(sizeof(int) * d_ * k_);
    linv = malloc(sizeof(int) * d_ * k_);
    nbr = malloc(sizeof(int) * (size_t)N_ * d_);
    cur = malloc(sizeof(u64) * N_);
    nxt = malloc(sizeof(u64) * N_);
    if (!pw || !mulT || !invT || !lay || !vol || !linv || !nbr || !cur || !nxt) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G_; x++)
        for (int y = 0; y < G_; y++)
            mulT[x * G_ + y] = gmul(x, y);
    for (int x = 0; x < G_; x++) {
        invT[x] = 0;
        for (int y = 0; y < G_; y++)
            if (mulT[x * G_ + y] == 0) { invT[x] = y; break; }
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) lay[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = lay[l * k_ + i];
            lay[l * k_ + i] = lay[l * k_ + j];
            lay[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) vol[l * k_ + i] = rint_(G_);
    }

    clock_t c0 = clock();
    long long cost = evaluate();
    const int NCYC = 3;
    double cyc = limit / NCYC;
    int cyc_id = -1;
    double T0 = 1.0, T1 = 0.05;
    while (cost > 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        int cid = (int)(el / cyc);
        if (cid != cyc_id) {
            cyc_id = cid;
            T0 = 0.05 * (double)cost;
            if (T0 < 1.0) T0 = 1.0;
        }
        double phase = (el - cid * cyc) / cyc;
        if (phase < 0) phase = 0;
        if (phase > 1) phase = 1;
        double T = T0 * pow(T1 / T0, phase);

        if (k_ >= 2 && rdbl() < 0.3) {
            int l = rint_(d_), i1 = rint_(k_), i2 = rint_(k_);
            if (i1 == i2) continue;
            int *p1 = &lay[l * k_ + i1], *p2 = &lay[l * k_ + i2];
            int t = *p1; *p1 = *p2; *p2 = t;
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                t = *p1; *p1 = *p2; *p2 = t;
            }
        } else {
            int idx = rint_(d_ * k_);
            int old = vol[idx];
            int nw = rint_(G_);
            if (nw == old) continue;
            vol[idx] = nw;
            long long nc = evaluate();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                vol[idx] = old;
            }
        }
    }

    if (cost != 0) { printf("0 0\n"); return 0; }
    build_nbr();
    int nL = k_ * G_;
    printf("%d %d\n", N_, nL * d_);
    for (int v = 0; v < nL; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nbr[v * d_ + l]);
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


def _groups_of_order(G, rng):
    """Return (m, k2, r) triples for every Z_m x| Z_k2 with m*k2 = G (one random valid r each)."""
    out = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m == 1:
            out.append((1, k2, 0))
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            out.append((m, k2, rng.choice(cands)))
    return out


def _run_lift(d, D, k, G, rng, seed, seconds):
    """Run the C lift search for base size k and a random group of order G. Returns (n, edges)."""
    m, k2, r = rng.choice(_groups_of_order(G, rng))
    out = lib.run_c(C_LIFT, [d, D, k, m, k2, r, seed, f"{seconds:.2f}"],
                    stdin_graph=None, timeout=seconds + 20.0)
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

    # Lift search: bandit over base sizes k, each try aims just above the best order.
    ks = [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 16]
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    lift_end = t0 + max(1.0, time_limit - 6.0)
    while True:
        remaining = lift_end - time.monotonic()
        if remaining < 1.5:
            break
        secs = min(max(2.0, remaining / 4.0), remaining - 0.5, 10.0)

        k = pick_k()
        gmin = best[0] // (2 * k) + 1          # smallest G with 2*k*G > best order
        G = gmin + rng.randrange(0, max(1, gmin // 40 + 1))
        if G > 2000:
            break
        trials[k] += 1
        try:
            n, e = _run_lift(d, D, k, G, rng, rng.randrange(1, 1 << 30), secs)
        except Exception:
            break  # keep the valid fallback
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
