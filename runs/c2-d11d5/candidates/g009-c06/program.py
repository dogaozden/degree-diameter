"""Bi-Cayley voltage-lift annealing over semidirect groups Z_m x| Z_k2, run in C.

New in this version:
- Block-representative cost: left multiplication by the group is an automorphism of a
  bi-Cayley lift, so diameter <= D holds iff BFS from the 2k block representatives reaches
  every vertex within D. Each evaluation is 2k truncated BFS passes instead of all-pairs bitsets.
- Layer-local rebuild: a move touches one permutation layer, so only that layer's neighbour
  table is recomputed.
- Ratcheted goal: Python passes its current best order to C; C only accepts larger lifts.
- Time-based annealing schedule, restarted over random (k, group, voltage) choices with a
  bandit over the base size k.

Every returned graph is checked with lib.is_valid; K_{d,d} or a classical construction is the fallback.
"""
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley lift annealing over Z_m x|_r Z_k2.
 * Usage:  prog d D seed time_limit [goal_n]
 * No stdin is read. stdout: "n m" + edges of the best lift found with n > goal_n,
 * or "0 0" when nothing better was found.
 *
 * Vertices: A-block i (i < K) is index i*G + g; B-block j is index (K+j)*G + h.
 * Layer l joins A-block i to B-block perm[l][i] with voltage vol[l][i]:
 *   A_{i,g} ~ B_{perm,g*s}.  Every layer is a perfect matching between the blocks,
 * so every vertex gets exactly d neighbour slots (duplicates are removed on output).
 * Left multiplication by the group is an automorphism, so the cost is the number of
 * (block representative, vertex) pairs at distance > D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 16384
#define MAXD 32
#define MAXK 4
#define MAXPW 64

typedef struct {
    int m, k2, G, r;
    int pw[MAXPW];
} Group;

static int d, D;
static int K, G, NN;
static Group grp;
static int perm[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int ivol[MAXD][MAXK];
static int nb[MAXN][MAXD];
static int vis[MAXN];
static int qbuf[MAXN];
static int stampv = 0;

static int bestK = 0;
static Group bestGrp;
static int bperm[MAXD][MAXK];
static int bvol[MAXD][MAXK];
static int trials[MAXK + 1], wins[MAXK + 1];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* (a,b)*(c,d) = (a + r^b c, b + d), element (a,b) coded as a*k2 + b. */
static int gmul(int x, int y) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long t = (long)grp.pw[b] * c;
    int ra = (int)((a + t) % m);
    int rb = (b + e) % k2;
    return ra * k2 + rb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b), with r^(-b) = r^(k2-b). */
static int ginv(int x) {
    int k2 = grp.k2, m = grp.m;
    int a = x / k2, b = x % k2;
    int nbk = (k2 - b) % k2;
    long t = (long)grp.pw[nbk] * a % m;
    int ia = (int)((m - t) % m);
    return ia * k2 + nbk;
}

static int sample_group(Group *g, int target) {
    static const int KS2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8,
                                9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    for (int tries = 0; tries < 300; tries++) {
        int k2 = KS2[rndi(20)];
        int m = (target + k2 - 1) / k2 + rndi(2);
        if (m < 2) m = 2;
        int r = 1 % m;
        if (k2 > 1) {
            int ok = 0;
            for (int t = 0; t < 80 && !ok; t++) {
                int c = 1 + rndi(m - 1);
                if (gcd_int(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    ok = 1;
                }
            }
            if (!ok) continue;
        }
        g->m = m;
        g->k2 = k2;
        g->r = r;
        g->G = m * k2;
        g->pw[0] = 1 % m;
        for (int t = 1; t < k2; t++) g->pw[t] = (int)((long)g->pw[t - 1] * r % m);
        return 1;
    }
    return 0;
}

/* Recompute neighbour slot l of every vertex from perm[l] and vol[l]. */
static void build_layer(int l) {
    int ip[MAXK];
    for (int i = 0; i < K; i++) ip[perm[l][i]] = i;
    for (int i = 0; i < K; i++) {
        int j = perm[l][i];
        for (int x = 0; x < G; x++)
            nb[i * G + x][l] = (K + j) * G + gmul(x, vol[l][i]);
    }
    for (int j = 0; j < K; j++) {
        int i = ip[j];
        for (int h = 0; h < G; h++)
            nb[(K + j) * G + h][l] = i * G + gmul(h, ivol[l][i]);
    }
}

/* Truncated BFS from each block representative (index b*G); returns total unreached pairs. */
static long cost_eval(void) {
    long total = 0;
    for (int b = 0; b < 2 * K; b++) {
        int s = b * G;
        int st = ++stampv;
        int head = 0, tail = 0;
        vis[s] = st;
        qbuf[tail++] = s;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            for (; head < end; head++) {
                int v = qbuf[head];
                for (int l = 0; l < d; l++) {
                    int u = nb[v][l];
                    if (vis[u] != st) {
                        vis[u] = st;
                        qbuf[tail++] = u;
                    }
                }
            }
        }
        total += NN - tail;
    }
    return total;
}

static void random_lift(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) {
            vol[l][i] = rndi(G);
            ivol[l][i] = ginv(vol[l][i]);
        }
    }
    for (int l = 0; l < d; l++) build_layer(l);
}

/* Time-based simulated annealing from a random lift. Returns the final cost (0 = success). */
static long anneal(double deadline) {
    random_lift();
    long cost = cost_eval();
    double c0 = (double)cost + 1.0;
    double T0 = 2.0 + 0.01 * c0;
    double tstart = now();
    double span = deadline - tstart;
    if (span < 1e-3) span = 1e-3;
    while (cost > 0) {
        double tn = now();
        if (tn > deadline) break;
        double frac = (tn - tstart) / span;
        double T = 0.3 + T0 * (1.0 - frac);
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndi(d);
            int i1 = rndi(K);
            int i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int t = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = t;
            build_layer(l);
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                t = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = t;
                build_layer(l);
            }
        } else {
            int l = rndi(d);
            int i = rndi(K);
            int nv = rndi(G);
            if (nv == vol[l][i]) continue;
            int ov = vol[l][i], oi = ivol[l][i];
            vol[l][i] = nv;
            ivol[l][i] = ginv(nv);
            build_layer(l);
            long c2 = cost_eval();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
            } else {
                vol[l][i] = ov;
                ivol[l][i] = oi;
                build_layer(l);
            }
        }
    }
    return cost;
}

static int pick_k(void) {
    if (rnd01() < 0.2) return 1 + rndi(4);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= 4; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) {
            bv = v;
            bk = k;
        }
    }
    return bk;
}

static void output_best(void) {
    K = bestK;
    grp = bestGrp;
    G = grp.G;
    NN = 2 * K * G;
    memcpy(perm, bperm, sizeof(perm));
    memcpy(vol, bvol, sizeof(vol));
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) ivol[l][i] = ginv(vol[l][i]);
    for (int l = 0; l < d; l++) build_layer(l);
    if (cost_eval() != 0) {
        printf("0 0\n");
        return;
    }
    long m = 0;
    int A = K * G;
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) {
            int v = nb[u][l], dup = 0;
            for (int q = 0; q < l; q++)
                if (nb[u][q] == v) {
                    dup = 1;
                    break;
                }
            if (!dup) m++;
        }
    printf("%d %ld\n", NN, m);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++) {
            int v = nb[u][l], dup = 0;
            for (int q = 0; q < l; q++)
                if (nb[u][q] == v) {
                    dup = 1;
                    break;
                }
            if (!dup) printf("%d %d\n", u, v);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double lim = atof(argv[4]);
    long best_n = argc > 5 ? atol(argv[5]) : 0;
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    double tend = now() + lim;
    int found = 0;
    while (now() < tend - 0.3) {
        int k = pick_k();
        double eps = 0.005 + 0.03 * rnd01();
        double want = (double)best_n * (1.0 + eps) + 2.0;
        int gt = (int)ceil(want / (2.0 * k));
        Group g;
        if (!sample_group(&g, gt)) continue;
        long Nc = 2L * k * g.G;
        if (Nc <= best_n || Nc > MAXN) continue;
        double remain = tend - now();
        double slice = 5.0 + 5.0 * rnd01();
        if (slice > remain - 0.2) slice = remain - 0.2;
        if (slice < 0.5) break;
        K = k;
        grp = g;
        G = g.G;
        NN = (int)Nc;
        trials[k]++;
        long c = anneal(now() + slice);
        if (c == 0) {
            wins[k]++;
            found = 1;
            best_n = NN;
            bestK = K;
            bestGrp = grp;
            memcpy(bperm, perm, sizeof(perm));
            memcpy(bvol, vol, sizeof(vol));
        }
    }
    if (found) output_best();
    else printf("0 0\n");
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
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the safe fallback for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(*pg)
        if D == 3 and lib.is_prime_power(d - 1):
            return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # C lift annealing, started with the ratcheted goal = current best order.
    used = time.monotonic() - t0
    budget = 0.85 * time_limit - 4.0 - used
    if budget >= 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                             stdin_graph=None, timeout=budget + 20)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    return best
