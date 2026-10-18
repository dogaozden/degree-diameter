"""Bold variant: C voltage-lift annealer over semidirect products with bases of 2..6 blocks per side.

Model. A bipartite graph is a lift of a d-regular bipartite base multigraph with k blocks per side.
Layer l is a permutation P_l of the k left blocks onto the k right blocks, and each dart carries a
voltage S in Z_m x| Z_k2. Left multiplication is an automorphism of the lift and acts regularly on
each block, so the lift has diameter <= D iff a BFS from the identity of each of the 2k blocks
reaches every vertex within D steps. Each evaluation therefore costs 2k BFS runs, which is far
cheaper than the Python bitset check. C anneals the voltages and layer permutations, and raises the
target order after each success.
"""
import time

import lib


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

#define MAXK2 64
#define BESTCAP (1 << 23)

static int dd, DD;           /* degree, diameter */
static int Kb, G, NN;        /* blocks per side, group order, vertices */
static int MM, K2, RR;       /* group Z_MM x| Z_K2 with r = RR, element a*K2+b */
static int pw[MAXK2];        /* pw[b] = RR^b mod MM */
static int *P, *Pinv, *S, *nbr, *vis, *que;
static int stamp = 1;
static int bestN = 0, bestM = 0;
static int *bestEu, *bestEv;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long a2 = ((long long)a + (long long)pw[b] * c) % MM;
    int b2 = (b + d) % K2;
    return (int)a2 * K2 + b2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long c = ((long long)((MM - a % MM) % MM) * pw[nb]) % MM;
    return (int)c * K2 + nb;
}

static int make_group(int g) {
    int divs[MAXK2], nd = 0;
    for (int k2 = 1; k2 <= g && k2 <= MAXK2; k2++)
        if (g % k2 == 0 && g / k2 >= 2) divs[nd++] = k2;
    if (nd == 0) return 0;
    K2 = divs[rint_(nd)];
    MM = g / K2;
    G = g;
    RR = 1 % MM;
    if (K2 > 1) {
        int found = 0;
        for (int t = 0; t < 400 && !found; t++) {
            int c = 1 + rint_(MM - 1);
            if (gcd_(c, MM) != 1) continue;
            long long p = 1;
            for (int e = 0; e < K2; e++) p = p * c % MM;
            if (p == 1 % MM) { RR = c; found = 1; }
        }
        if (!found) { K2 = 1; MM = g; RR = 1 % g; }
    }
    pw[0] = 1 % MM;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * RR % MM);
    return 1;
}

/* Rebuild the neighbour entries of layer l for left block i and right block P[l][i]. */
static void refresh(int l, int i) {
    int idx = l * Kb + i;
    int j = P[idx], s = S[idx];
    int si = ginv(s);
    for (int x = 0; x < G; x++) {
        int v = i * G + x;
        nbr[v * dd + l] = (Kb + j) * G + gmul(x, s);
        int w = (Kb + j) * G + x;
        nbr[w * dd + l] = i * G + gmul(x, si);
    }
}

/* Number of (block source, vertex) pairs at distance > DD, summed over the 2*Kb sources. */
static long long cost_eval(void) {
    long long unreached = 0;
    if (stamp > 1000000000) {
        memset(vis, 0, sizeof(int) * (size_t)NN);
        stamp = 1;
    }
    for (int b = 0; b < 2 * Kb; b++) {
        stamp++;
        int head = 0, tail = 0;
        int src = b * G;
        vis[src] = stamp;
        que[tail++] = src;
        for (int depth = 0; depth < DD && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int v = que[head++];
                const int *nv = nbr + (size_t)v * dd;
                for (int l = 0; l < dd; l++) {
                    int u = nv[l];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            }
        }
        unreached += NN - tail;
    }
    return unreached;
}

static void save_best(void) {
    if ((long long)NN * dd > BESTCAP) return;
    int m = 0;
    for (int v = 0; v < NN; v++) {
        for (int l = 0; l < dd; l++) {
            int u = nbr[v * dd + l];
            if (u <= v) continue;
            int dup = 0;
            for (int l2 = 0; l2 < l; l2++) if (nbr[v * dd + l2] == u) { dup = 1; break; }
            if (dup) continue;
            bestEu[m] = v;
            bestEv[m] = u;
            m++;
        }
    }
    bestN = NN;
    bestM = m;
}

static void init_lift(void) {
    int perm[MAXK2];
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < Kb; i++) perm[i] = i;
        for (int i = Kb - 1; i > 0; i--) {
            int r = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[r]; perm[r] = t;
        }
        for (int i = 0; i < Kb; i++) {
            P[l * Kb + i] = perm[i];
            Pinv[l * Kb + perm[i]] = i;
        }
    }
    for (int idx = 0; idx < dd * Kb; idx++) S[idx] = rint_(G);
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < Kb; i++) refresh(l, i);
}

static void alloc_attempt(void) {
    P = malloc(sizeof(int) * (size_t)dd * Kb);
    Pinv = malloc(sizeof(int) * (size_t)dd * Kb);
    S = malloc(sizeof(int) * (size_t)dd * Kb);
    nbr = malloc(sizeof(int) * (size_t)NN * dd);
    vis = calloc((size_t)NN, sizeof(int));
    que = malloc(sizeof(int) * (size_t)NN);
}

static void free_attempt(void) {
    free(P); free(Pinv); free(S); free(nbr); free(vis); free(que);
    P = Pinv = S = nbr = vis = que = NULL;
}

/* Simulated annealing on voltages and layer permutations. Returns 1 when a valid lift is found. */
static int anneal(double slice, clock_t t0, double TL) {
    const double T0 = 30.0, T1 = 0.5;
    clock_t ts = clock();
    long long cur = cost_eval();
    if (cur == 0) { save_best(); return 1; }
    for (;;) {
        double el = (double)(clock() - ts) / CLOCKS_PER_SEC;
        if (el >= slice) break;
        if ((double)(clock() - t0) / CLOCKS_PER_SEC >= TL) break;
        double T = T0 * pow(T1 / T0, el / slice);
        int l = rint_(dd), i = rint_(Kb);
        int idx = l * Kb + i;
        if (rdbl() < 0.7) {
            int oldS = S[idx];
            int ns = rint_(G);
            if (ns == oldS) continue;
            S[idx] = ns;
            refresh(l, i);
            long long c2 = cost_eval();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                if (cur == 0) { save_best(); return 1; }
            } else {
                S[idx] = oldS;
                refresh(l, i);
            }
        } else {
            int i2 = rint_(Kb);
            if (i2 == i) continue;
            int idx2 = l * Kb + i2;
            int j1 = P[idx], j2 = P[idx2];
            P[idx] = j2; P[idx2] = j1;
            Pinv[l * Kb + j2] = i;
            Pinv[l * Kb + j1] = i2;
            refresh(l, i);
            refresh(l, i2);
            long long c2 = cost_eval();
            if (c2 <= cur || rdbl() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                if (cur == 0) { save_best(); return 1; }
            } else {
                P[idx] = j1; P[idx2] = j2;
                Pinv[l * Kb + j1] = i;
                Pinv[l * Kb + j2] = i2;
                refresh(l, i);
                refresh(l, i2);
            }
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double TL = atof(argv[4]);
    int target = atoi(argv[5]);
    if (dd < 3 || DD < 3 || target < 2) { printf("0 0\n"); return 0; }
    bestEu = malloc(sizeof(int) * BESTCAP);
    bestEv = malloc(sizeof(int) * BESTCAP);
    if (!bestEu || !bestEv) { printf("0 0\n"); return 0; }

    clock_t t0 = clock();
    int fails = 0;
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        double rem = TL - el;
        if (rem < 0.2) break;
        int k = 2 + rint_(5);
        int g = (target + 2 * k - 1) / (2 * k);
        if (g < 2) g = 2;
        if (!make_group(g)) break;
        Kb = k;
        NN = 2 * Kb * G;
        if ((long long)NN * dd > BESTCAP) {
            target = (int)(target * 0.9);
            if (target < 4) target = 4;
            continue;
        }
        alloc_attempt();
        init_lift();
        double slice = 2.0 + 0.5 * fails;
        if (slice > rem) slice = rem;
        int ok = anneal(slice, t0, TL);
        free_attempt();
        if (ok) {
            fails = 0;
            target = bestN + 1;
        } else {
            fails++;
            if (bestN == 0) target = (int)(target * 0.9);
            if (target < 4) target = 4;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestEu[i], bestEv[i]);
    return 0;
}
"""


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _consider(best, n, e, d, D):
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = max(2, 2 * D)
        if n == 2:
            return 2, [(0, 1)]
        return n, [(i, (i + 1) % n) for i in range(n)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid safe fallback for D >= 2
    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            best = _consider(best, pg[0], pg[1], d, D)
            if lib.is_prime_power(d - 1):
                return best

    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining - 6.0
    if budget >= 3.0:
        moore = lib.moore_bound(d, D)
        tstart = max(best[0] + 1, int(0.27 * moore))
        tstart = min(tstart, 60000)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", tstart],
                            timeout=budget + 15.0)
            cn, ce = lib.parse_graph_text(out)
            best = _consider(best, cn, ce, d, D)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
