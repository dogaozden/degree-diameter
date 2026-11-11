"""Bold variant: a pure-C bi-Cayley lift search over Z_m x| Z_k with base size k in 1..8.

Each candidate is a lift of a k+k base multigraph (d perfect matchings between the two
sides, each dart carrying a group voltage), searched by simulated annealing with an
incremental bitmask reachability cost. The engine works on the quotient, so it runs many
more evaluations per second than the numpy version. Exact constructions and K_{d,d} remain
as fallbacks, and every returned graph passes lib.is_valid.
"""
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage lifts over semidirect products, simulated annealing.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
/* Bi-Cayley lift search.
 * Usage: prog d D seed time_limit [min_n]
 * Searches for a d-regular bipartite lift of a k+k base multigraph over a group
 * G = Z_m x| Z_k2 (left-regular action on each block) with diameter <= D and order > min_n.
 * Output: "n m" + edge lines for the best found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXK 8
#define MAXL 32
#define MAXV 8192
#define MAXN 8192
#define MAXE (MAXL * MAXV / 2)

static int d, D, minN;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long inv_mod(long a, long m) {
    long t = 0, nt = 1, r = m, nr = a % m;
    while (nr != 0) {
        long q = r / nr;
        long tmp = t - q * nt; t = nt; nt = tmp;
        tmp = r - q * nr; r = nr; nr = tmp;
    }
    if (t < 0) t += m;
    return t % m;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---- group Z_gm x| Z_gk, element x = a*gk + b, (a,b)(c,e) = (a + r^b c, b + e) ---- */
static int gm, gk, gr, gN;
static int rp[MAXN], ginv[MAXN];

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gk + (b + e) % gk;
}

static void set_group(int m, int k2, int r) {
    gm = m; gk = k2; gr = r; gN = m * k2;
    rp[0] = 1 % m;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < gN; x++) {
        int a = x / gk, b = x % gk;
        int e = (gk - b) % gk;
        long ib = inv_mod(rp[b], m);
        long c = ((long)(m - a) % m) * ib % m;
        ginv[x] = (int)(c * gk + e);
    }
}

static int pick_group(int N) {
    int divs[128], nd = 0;
    for (int k2 = 1; k2 <= N && nd < 128; k2++)
        if (N % k2 == 0) divs[nd++] = k2;
    static int cand[MAXN];
    for (int tries = 0; tries < 4 * nd; tries++) {
        int k2 = divs[rndint(nd)];
        int m = N / k2;
        int nc = 0;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cand[nc++] = r;
        }
        if (nc) {
            set_group(m, k2, cand[rndint(nc)]);
            return 1;
        }
    }
    return 0;
}

/* ---- lift state: K blocks per side, d layers; layer l maps A-block i to B-block pi[l][i]
 * with voltage sv[l][i]: A(i,g) ~ B(pi, g*s). Vertex ids: block b, element g -> b*gN + g,
 * A blocks are 0..K-1, B blocks are K..2K-1. ---- */
static int K, NV;
static int pi_[MAXL][MAXK], pinv_[MAXL][MAXK], sv_[MAXL][MAXK];
static int nb[MAXL][MAXV];
static uint32_t MA[MAXV], MB[MAXV];
static int eu[MAXE], ev[MAXE], ne = 0, saved_n = 0;

static void rebuild_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = pi_[l][i], s = sv_[l][i];
        for (int g = 0; g < gN; g++)
            nb[l][i * gN + g] = (K + j) * gN + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = pinv_[l][j];
        int si = ginv[sv_[l][i]];
        for (int h = 0; h < gN; h++)
            nb[l][(K + j) * gN + h] = i * gN + gmul(h, si);
    }
}

static int dart_ok(int l, int i) {
    for (int t = 0; t < d; t++)
        if (t != l && pi_[t][i] == pi_[l][i] && sv_[t][i] == sv_[l][i]) return 0;
    return 1;
}

static int random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) pi_[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = pi_[l][i]; pi_[l][i] = pi_[l][j]; pi_[l][j] = t;
        }
        for (int i = 0; i < K; i++) pinv_[l][pi_[l][i]] = i;
        for (int i = 0; i < K; i++) sv_[l][i] = rndint(gN);
    }
    for (int iter = 0;; iter++) {
        int bad = 0;
        for (int l = 0; l < d; l++)
            for (int i = 0; i < K; i++)
                if (!dart_ok(l, i)) { sv_[l][i] = rndint(gN); bad = 1; }
        if (!bad) break;
        if (iter >= 100000) return 0;
    }
    for (int l = 0; l < d; l++) rebuild_layer(l);
    return 1;
}

/* Bitmask propagation over the lift: bit b of mask[v] is set when representative of block b
 * is within distance D of v. Cost = number of missing (vertex, block) pairs. */
static int eval_cost(void) {
    uint32_t full = (1u << (2 * K)) - 1u;
    uint32_t *cur = MA, *nxt = MB;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * gN] = 1u << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < NV; v++) {
            uint32_t m = cur[v];
            for (int l = 0; l < d; l++) m |= cur[nb[l][v]];
            nxt[v] = m;
        }
        uint32_t *t = cur; cur = nxt; nxt = t;
    }
    int cost = 0;
    for (int v = 0; v < NV; v++)
        cost += 2 * K - __builtin_popcount(cur[v] & full);
    return cost;
}

static void save_solution(void) {
    ne = 0;
    saved_n = NV;
    int half = K * gN;
    for (int l = 0; l < d; l++)
        for (int v = 0; v < half; v++) {
            if (ne >= MAXE) return;
            eu[ne] = v;
            ev[ne] = nb[l][v];
            ne++;
        }
}

static int sa_run(long patience) {
    if (!random_state()) return 0;
    int cost = eval_cost();
    int best = cost;
    long last = 0;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > t_end) return 0;
        if (it - last > patience) return 0;
        double ph = (double)(it % 20000) / 20000.0;
        double T = 0.25 + 1.5 * (1.0 - ph) * (1.0 - ph);
        int l = rndint(d), i = rndint(K);
        if (K >= 2 && rnd01() < 0.3) {
            int i2 = rndint(K - 1);
            if (i2 >= i) i2++;
            int j1 = pi_[l][i], j2 = pi_[l][i2];
            pi_[l][i] = j2; pi_[l][i2] = j1;
            pinv_[l][j2] = i; pinv_[l][j1] = i2;
            if (!dart_ok(l, i) || !dart_ok(l, i2)) {
                pi_[l][i] = j1; pi_[l][i2] = j2;
                pinv_[l][j1] = i; pinv_[l][j2] = i2;
                continue;
            }
            rebuild_layer(l);
            int nc = eval_cost();
            int delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                pi_[l][i] = j1; pi_[l][i2] = j2;
                pinv_[l][j1] = i; pinv_[l][j2] = i2;
                rebuild_layer(l);
            }
        } else {
            int old = sv_[l][i];
            int ns = rndint(gN);
            if (ns == old) continue;
            sv_[l][i] = ns;
            if (!dart_ok(l, i)) { sv_[l][i] = old; continue; }
            rebuild_layer(l);
            int nc = eval_cost();
            int delta = nc - cost;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cost = nc;
            } else {
                sv_[l][i] = old;
                rebuild_layer(l);
            }
        }
        if (cost < best) { best = cost; last = it; }
    }
}

static void search(void) {
    long moore = moore_bound();
    long bestN = minN;
    long fails = 0;
    while (now() < t_end) {
        int k = 1 + rndint(MAXK);
        long lo = (bestN + 2L * k) / (2L * k);   /* smallest N with 2kN > bestN */
        if (lo < d) lo = d;
        long N = lo + rndint(3);
        long nv = 2L * k * N;
        if (nv > moore || nv > MAXV || N > MAXN) {
            if (++fails > 100000) return;
            continue;
        }
        if (!pick_group((int)N)) continue;
        K = k;
        gN = (int)N;
        NV = (int)nv;
        long patience = (long)(3e8 / ((double)NV * d));
        if (patience < 5000) patience = 5000;
        if (sa_run(patience)) {
            save_solution();
            bestN = NV;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    minN = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.97 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d >= 3 && d <= MAXL && D >= 2 && moore_bound() > minN)
        search();

    if (ne > 0) {
        printf("%d %d\n", saved_n, ne);
        for (int i = 0; i < ne; i++)
            printf("%d %d\n", eu[i], ev[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions and driver.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, bipartite, degree d.
    best = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
        if lib.is_prime_power(d - 1):
            return best  # Moore-optimal
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                if ar[0] > best[0] and lib.is_valid(ar[0], ar[1], d, D):
                    best = ar
            except (ValueError, RuntimeError):
                pass

    if best[0] >= moore or time.monotonic() > end - 1.0:
        return best

    budget = end - time.monotonic() - 0.5
    if budget > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                             stdin_graph=None, timeout=budget + 6)
            n, edges = lib.parse_graph_text(text)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
