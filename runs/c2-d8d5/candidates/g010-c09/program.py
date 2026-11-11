import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over semidirect products Z_m x| Z_K2.
#
# A graph is a k-block lift: side A has blocks 0..k-1, side B has blocks k..2k-1,
# each block a copy of a group G of order m*K2. Each layer l pairs A-block i with
# B-block lay[l][i] through a voltage s, so A-vertex (i,x) joins (j, x*s). With d
# layers the graph is d-regular and bipartite, and left multiplication by any group
# element is an automorphism. Hence checking distances from the 2k block identities
# is exact. The annealer minimises the number of unreached (identity, vertex) pairs.
# The target order grows adaptively above the best order found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define DUP_PEN 4

static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long powmod_ll(long long b, long long e, long long mod) {
    long long r = 1 % mod;
    b %= mod;
    if (b < 0) b += mod;
    while (e > 0) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x| Z_K2: element a*K2 + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod K2). */
static int gm = 2, gK2 = 1, gG = 2;
static long long gpw[64];

static int gmul(int x, int y) {
    int a = x / gK2, b = x % gK2;
    int c = y / gK2, e = y % gK2;
    long long ra = ((long long)a + gpw[b] * (long long)c) % gm;
    int rb = (b + e) % gK2;
    return (int)(ra * gK2 + rb);
}

static int ginv(int x) {
    int a = x / gK2, b = x % gK2;
    int nb = (gK2 - b) % gK2;
    long long ia = (gpw[nb] * (long long)a) % gm;
    ia = (gm - ia) % gm;
    return (int)(ia * gK2 + nb);
}

/* Lift state. */
static int dd = 8, DD = 5, KK = 1, NN = 2;
static int *lay = NULL, *Sv = NULL, *nbr = NULL;
static u64 *bufA = NULL, *bufB = NULL, *lastR = NULL;
static u64 fullmask = 3ULL;

/* Best valid graph found so far. */
static int best_n = 0, best_m = 0, found_any = 0;
static int *best_eu = NULL, *best_ev = NULL;

static void set_dart(int l, int i) {
    int idx = l * KK + i;
    int j = lay[idx];
    int s = Sv[idx];
    int si = ginv(s);
    int A = i * gG, B = (KK + j) * gG;
    for (int x = 0; x < gG; x++) {
        nbr[(size_t)(A + x) * dd + l] = B + gmul(x, s);
        nbr[(size_t)(B + x) * dd + l] = A + gmul(x, si);
    }
}

/* Cost = unreached (block identity, vertex) pairs + duplicate-dart penalty. */
static long long evaluate(void) {
    int N = NN, d = dd, full = 2 * KK;
    u64 *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < full; b++) cur[(size_t)b * gG] |= 1ULL << b;
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            const int *nb = nbr + (size_t)v * d;
            u64 x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    lastR = cur;
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += full - __builtin_popcountll(cur[v]);
    long long dup = 0;
    for (int i = 0; i < KK; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (lay[l1 * KK + i] == lay[l2 * KK + i] && Sv[l1 * KK + i] == Sv[l2 * KK + i])
                    dup++;
    return unr + (long long)DUP_PEN * dup;
}

static void save_graph(void) {
    int d = dd;
    int An = KK * gG;
    int cap = An * d + 4;
    int *eu = malloc(sizeof(int) * (size_t)cap);
    int *ev = malloc(sizeof(int) * (size_t)cap);
    if (!eu || !ev) { free(eu); free(ev); return; }
    int m = 0;
    for (int v = 0; v < An; v++) {
        const int *nb = nbr + (size_t)v * d;
        for (int l = 0; l < d; l++) {
            int dup = 0;
            for (int q = 0; q < l; q++) if (nb[q] == nb[l]) { dup = 1; break; }
            if (!dup && m < cap) { eu[m] = v; ev[m] = nb[l]; m++; }
        }
    }
    free(best_eu); free(best_ev);
    best_eu = eu; best_ev = ev; best_m = m; best_n = NN; found_any = 1;
}

/* One annealing attempt for a fixed group and block count. Returns 1 on success. */
static int run_attempt(int k, int G, int K2, int m, int r, int d, int D,
                       double tend, long long *evals) {
    KK = k; gG = G; gK2 = K2; gm = m;
    gpw[0] = 1 % m;
    for (int t = 1; t < K2; t++) gpw[t] = (gpw[t - 1] * r) % m;
    NN = 2 * k * G; dd = d; DD = D;
    fullmask = (1ULL << (2 * k)) - 1ULL;

    lay = malloc(sizeof(int) * (size_t)(d * k));
    Sv = malloc(sizeof(int) * (size_t)(d * k));
    nbr = malloc(sizeof(int) * (size_t)NN * (size_t)d);
    bufA = malloc(sizeof(u64) * (size_t)NN);
    bufB = malloc(sizeof(u64) * (size_t)NN);
    int ok = 0;

    if (lay && Sv && nbr && bufA && bufB) {
        for (int l = 0; l < d; l++) {
            int *p = lay + (size_t)l * k;
            for (int i = 0; i < k; i++) p[i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            for (int i = 0; i < k; i++) Sv[l * k + i] = rint_(G);
        }
        for (int l = 0; l < d; l++)
            for (int i = 0; i < k; i++) set_dart(l, i);

        long long cost = evaluate();
        double c0 = (double)cost;
        if (c0 < 1.0) c0 = 1.0;
        double T0 = 0.02 * c0 + 2.0, T1 = 0.3;
        double tstart = now_sec();
        double span = tend - tstart;
        if (span < 1e-3) span = 1e-3;

        while (cost > 0) {
            double now = now_sec();
            if (now >= tend) break;
            (*evals)++;
            double frac = (now - tstart) / span;
            if (frac > 1.0) frac = 1.0;
            double T = T0 * pow(T1 / T0, frac);
            int mv = rint_(100);

            if (k >= 2 && mv < 15) {
                /* Swap the B-blocks of two darts in one layer. */
                int l = rint_(d);
                int i1 = rint_(k), i2 = rint_(k - 1);
                if (i2 >= i1) i2++;
                int *p1 = &lay[l * k + i1], *p2 = &lay[l * k + i2];
                int tmp = *p1; *p1 = *p2; *p2 = tmp;
                set_dart(l, i1); set_dart(l, i2);
                long long nc = evaluate();
                long long dl = nc - cost;
                if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                    cost = nc;
                } else {
                    tmp = *p1; *p1 = *p2; *p2 = tmp;
                    set_dart(l, i1); set_dart(l, i2);
                }
            } else {
                /* Voltage change, aimed at a bad vertex half the time. */
                int l = -1, i = -1;
                if (mv < 60) {
                    int v0 = rint_(NN), found = -1;
                    for (int q = 0; q < NN; q++) {
                        int v = v0 + q;
                        if (v >= NN) v -= NN;
                        if (lastR[v] != fullmask) { found = v; break; }
                    }
                    if (found >= 0) {
                        int b = found / gG;
                        l = rint_(d);
                        if (b < k) {
                            i = b;
                        } else {
                            int j = b - k;
                            for (int ii = 0; ii < k; ii++)
                                if (lay[l * k + ii] == j) { i = ii; break; }
                        }
                    }
                }
                if (i < 0) { l = rint_(d); i = rint_(k); }
                int idx = l * k + i;
                int old = Sv[idx];
                int nw = rint_(G);
                if (nw == old) continue;
                Sv[idx] = nw;
                set_dart(l, i);
                long long nc = evaluate();
                long long dl = nc - cost;
                if (dl <= 0 || rdbl() < exp(-(double)dl / T)) {
                    cost = nc;
                } else {
                    Sv[idx] = old;
                    set_dart(l, i);
                }
            }
        }
        ok = (cost == 0);
        if (ok) save_graph();
    }

    free(lay); free(Sv); free(nbr); free(bufA); free(bufB);
    lay = NULL; Sv = NULL; nbr = NULL; bufA = NULL; bufB = NULL; lastR = NULL;
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    long long start_n = argc > 5 ? atoll(argv[5]) : 0;

    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > 64 || D < 2 || limit <= 0.5 || start_n < 0) {
        printf("0 0\n");
        return 0;
    }

    double deadline = now_sec() + limit;
    int cur_n = (int)start_n;
    double eps = 0.02;
    int fails = 0;
    long long evals = 0;
    static const int kset[10] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 8};
    static const int k2set[12] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16};

    while (1) {
        double remain = deadline - now_sec();
        if (remain < 0.3) break;
        double alen = remain / 8.0;
        if (alen < 1.0) alen = remain;

        int k = kset[rint_(10)];
        long long delta = (long long)((double)cur_n * eps);
        if (delta < 2) delta = 2;
        long long Ntar = (long long)cur_n + delta;
        long long Gmin = (Ntar + 2LL * k - 1) / (2LL * k);
        if (Gmin < 2) Gmin = 2;
        int K2 = k2set[rint_(12)];
        long long mm = (Gmin + K2 - 1) / K2 + rint_(3);
        if (mm < 2) mm = 2;
        int m = (int)mm;

        int *cand = malloc(sizeof(int) * (size_t)m);
        if (!cand) break;
        int nc = 0;
        for (int c = 1; c < m; c++)
            if (powmod_ll(c, K2, m) == (long long)(1 % m)) cand[nc++] = c;
        if (nc < 1) { free(cand); continue; }
        int r = cand[rint_(nc)];
        free(cand);

        int G = m * K2;
        int N = 2 * k * G;
        double tend = now_sec() + alen;
        if (tend > deadline) tend = deadline;

        int ok = run_attempt(k, G, K2, m, r, d, D, tend, &evals);
        if (ok) {
            cur_n = N;
            fails = 0;
            eps *= 1.5;
            if (eps > 0.03) eps = 0.03;
        } else {
            fails++;
            if (fails >= 4) {
                eps *= 0.5;
                if (eps < 0.001) eps = 0.001;
                fails = 0;
            }
        }
    }

    if (!found_any) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_eu[i], best_ev[i]);
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, list(e))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best  # exact Moore-type construction, nothing to improve
        if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Lift search in C, seeded with the best order found so far.
    spent = time.monotonic() - t0
    budget = 0.85 * time_limit - 4.0 - spent
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, int(seed) & 0x7FFFFFFF, f"{budget:.2f}", best[0]],
                            stdin_graph=None, timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    return best
