"""Bi-Cayley voltage-lift search over semidirect groups, run entirely inside one C engine.

New in this version: the C engine (1) checks coverage over only the 2k block representatives
(valid because left multiplication by the group is an automorphism that is transitive on each
block), (2) anneals voltages and layer permutations with directed moves that target vertices
still out of reach, (3) runs iterated local search: after a stall it restores the best state,
kicks three darts, and continues, and (4) chooses base size k with a bandit and ratchets the
order goal. Python handles only the exact small constructions, the call, and validation.
Every returned graph is checked with lib.is_valid, and K_{d,d} (or a known construction) is the fallback.
"""
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXN 12288
#define MAXE 400000
#define PEN 8
#define KMAXUSE 4
#define NK2 11

static const int K2LIST[NK2] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Group Z_M x|_r Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int M, K2, G, KB, NN;
static int pw[64];

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int setup_group(long target, int k2) {
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    if (m * k2 > MAXN / 2) return 0;
    if (k2 == 1) {
        M = (int)m;
        K2 = 1;
        G = M;
        pw[0] = 1;
        return 1;
    }
    for (int tries = 0; tries < 200; tries++) {
        long r;
        double u = rnd01();
        if (u < 0.3 || m == 2) r = 1;
        else if (u < 0.4 && k2 % 2 == 0) r = m - 1;
        else r = 1 + rndint((int)(m - 1));
        if (gcd_i((int)r, (int)m) != 1) continue;
        long p = 1 % m;
        for (int b = 0; b < k2; b++) {
            pw[b] = (int)p;
            p = p * r % m;
        }
        if (p == 1 % m) {
            M = (int)m;
            K2 = k2;
            G = M * k2;
            return 1;
        }
    }
    return 0;
}

static inline int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    int ra = (int)(((long)a + (long)pw[b] * c) % M);
    int rb = b + e;
    if (rb >= K2) rb -= K2;
    return ra * K2 + rb;
}

static inline int ginv(int s) {
    int a = s / K2, b = s - a * K2;
    int nb = (K2 - b) % K2;
    long c = (-(long)pw[nb] * a) % M;
    if (c < 0) c += M;
    return (int)c * K2 + nb;
}

/* Lift state: layer l joins A-block i to B-block perm[l][i] with voltage sv[l][i]. */
static int perm[MAXD][MAXK];
static int sv[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t cur[MAXN], nxt[MAXN];
static int bperm[MAXD][MAXK], bsv[MAXD][MAXK];

static int best_n = 0, best_m = 0;
static int beu[MAXE], bev[MAXE];
static int trials[MAXK + 1], wins[MAXK + 1];

static void swap_perm(int l, int i, int j) {
    int t = perm[l][i];
    perm[l][i] = perm[l][j];
    perm[l][j] = t;
}

static void set_dart(int l, int i) {
    int p = perm[l][i], s = sv[l][i], si = ginv(s);
    int ia = i * G, ib = (KB + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ia + g] = ib + gmul(g, s);
        nbr[l][ib + g] = ia + gmul(g, si);
    }
}

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) perm[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < KB; i++) sv[l][i] = rndint(G);
    }
}

static void rebuild_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i);
}

/* Sum over all vertices of the number of block representatives NOT within distance D.
 * Zero means every pair is within distance D. */
static long eval_unreached(void) {
    int W = 2 * KB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)NN);
    for (int b = 0; b < W; b++) cur[b * G] |= 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        memcpy(cur, nxt, sizeof(uint32_t) * (size_t)NN);
        if (!changed) break;
    }
    long un = 0;
    for (int v = 0; v < NN; v++) un += W - __builtin_popcount(cur[v]);
    return un;
}

/* Duplicate darts (same block pair and same voltage in two layers) give parallel edges. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (perm[l1][i] == perm[l2][i] && sv[l1][i] == sv[l2][i]) c++;
    return c;
}

static long lift_cost(void) {
    long u = eval_unreached();
    return u + (long)PEN * dup_count();
}

static void save_best(void) {
    memcpy(bperm, perm, sizeof perm);
    memcpy(bsv, sv, sizeof sv);
}

static void restore_best(void) {
    memcpy(perm, bperm, sizeof perm);
    memcpy(sv, bsv, sizeof sv);
}

/* Pick a dart, biased toward a vertex that is still out of reach (last evaluated state). */
static void pick_dart(int *lo, int *io) {
    uint32_t full = (uint32_t)((1u << (2 * KB)) - 1);
    if (rnd01() < 0.5) {
        for (int t = 0; t < 30; t++) {
            int v = rndint(NN);
            if (cur[v] == full) continue;
            int b = v / G;
            int l = rndint(d);
            if (b < KB) {
                *lo = l;
                *io = b;
                return;
            }
            int j = b - KB, found = -1;
            for (int i = 0; i < KB; i++)
                if (perm[l][i] == j) {
                    found = i;
                    break;
                }
            if (found >= 0) {
                *lo = l;
                *io = found;
                return;
            }
        }
    }
    *lo = rndint(d);
    *io = rndint(KB);
}

static int accept(long c2, long c1, double T) {
    if (c2 <= c1) return 1;
    return rnd01() < exp(-(double)(c2 - c1) / T);
}

/* Anneal one lift (fixed k, group). Returns 1 if the current state is valid. */
static int run_lift(double deadline, long max_evals, long patience) {
    init_random();
    rebuild_all();
    long cost = lift_cost();
    long best = cost;
    save_best();
    long stall = 0;
    int kicks = 0;
    for (long ev = 0; ev < max_evals && cost > 0; ev++) {
        if ((ev & 7) == 0 && now() > deadline) break;
        if (stall > patience) {
            if (kicks >= 3) break;
            kicks++;
            restore_best();
            for (int t = 0; t < 3; t++) {
                int l = rndint(d), i = rndint(KB);
                sv[l][i] = rndint(G);
            }
            rebuild_all();
            cost = lift_cost();
            stall = 0;
            continue;
        }
        double T = 0.1 + 0.8 * (1.0 - (double)ev / (double)max_evals);
        if (KB > 1 && rnd01() < 0.2) {
            int l = rndint(d), i = rndint(KB), j = rndint(KB - 1);
            if (j >= i) j++;
            swap_perm(l, i, j);
            set_dart(l, i);
            set_dart(l, j);
            long c2 = lift_cost();
            if (accept(c2, cost, T)) {
                cost = c2;
            } else {
                swap_perm(l, i, j);
                set_dart(l, i);
                set_dart(l, j);
            }
        } else {
            int l, i;
            pick_dart(&l, &i);
            int old = sv[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            sv[l][i] = nw;
            set_dart(l, i);
            long c2 = lift_cost();
            if (accept(c2, cost, T)) {
                cost = c2;
            } else {
                sv[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < best) {
            best = cost;
            save_best();
            stall = 0;
        } else {
            stall++;
        }
    }
    return cost == 0;
}

static void record(void) {
    long m = (long)KB * G * d;
    if (m > MAXE) return;
    int c = 0;
    for (int u = 0; u < KB * G; u++)
        for (int l = 0; l < d; l++) {
            beu[c] = u;
            bev[c] = nbr[l][u];
            c++;
        }
    best_n = NN;
    best_m = c;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndint(KMAXUSE);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= KMAXUSE; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start_n = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit - 1.0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    best_n = (int)start_n;
    best_m = 0;
    if (d < 3 || d > MAXD || D < 3 || limit < 2.0) {
        printf("0 0\n");
        return 0;
    }
    double goal = start_n > 0 ? 1.05 * (double)start_n : 2.0 * d;
    while (now() < t_end) {
        int k = pick_k();
        int k2 = K2LIST[rndint(NK2)];
        long target = (long)(goal / (2.0 * k)) + rndint(3);
        if (target < 2) target = 2;
        if (!setup_group(target, k2)) continue;
        KB = k;
        NN = 2 * KB * G;
        if (NN > MAXN) continue;
        if (NN <= best_n) {
            double floorv = 1.02 * (double)best_n;
            if (goal < floorv) goal = floorv;
            continue;
        }
        trials[k]++;
        double remaining = t_end - now();
        double slice = remaining / 5.0;
        if (slice < 3.0) slice = 3.0;
        if (slice > remaining) slice = remaining;
        int ok = run_lift(now() + slice, 60000, 2500);
        if (ok && NN > best_n) {
            wins[k]++;
            record();
            goal = 1.04 * (double)NN;
        } else {
            double floorv = 1.02 * (double)best_n;
            goal = goal * 0.99;
            if (goal < floorv) goal = floorv;
        }
    }
    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int e = 0; e < best_m; e++) printf("%d %d\n", beu[e], bev[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # One C run does all the lift search. Reserve time for compiling, parsing and validation.
    if d >= 3 and D >= 3:
        remaining = time_limit - (time.monotonic() - t0) - 6.0
        if remaining > 3.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                                 timeout=remaining + 15.0)
                consider(*lib.parse_graph_text(text))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
