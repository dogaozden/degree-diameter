"""Combined program: exact projective-plane and generalized-quadrangle constructions, then a C
bi-Cayley voltage-lift search over semidirect groups Z_m x| Z_k2 with base sizes k = 1..6.

Change in this version: the lift annealing moved from numpy into C. Each cost evaluation is a
bitset-style reach pass over block representatives, and group sampling, bandit over k and the
order ratchet all run inside one C process. The Python side keeps the constructions, the
fallback and the final lib.is_valid check.

Every returned graph is checked with lib.is_valid, and K_{d,d} is the fallback.
"""
import itertools
import time

import lib


C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley voltage-lift search.
 * Group: Z_m x|_r Z_k2, element (a,b) coded as a*k2+b, product (a,b)(c,e) = (a + r^b c, b+e).
 * Base: K blocks per side. A(i,g) = i*G+g, B(j,h) = (K+j)*G+h.
 * Layer l pairs A block i with B block perm[l][i] through voltage S[l][i]:
 *   A(i,g) ~ B(perm[l][i], g*s), equivalently B(j,h) ~ A(i, h*s^-1).
 * Every layer is a permutation, so the graph is d-regular and bipartite.
 * Left multiplication is an automorphism, so the cost counts (block representative, vertex)
 * pairs at distance > D plus PEN per duplicate dart, and cost 0 means diameter <= D.
 * Usage: prog d D seed time_limit goal_n   (stdin ignored)
 * stdout: "n m" + edges of the best lift with n > goal_n, or "0 0".
 */

#define MAXD 40
#define MAXK 8
#define KMAX 6
#define MAXN 40000
#define MAXG (MAXN / 2)
#define PEN 1000L

static int d, D, K, G, NV;
static int gm, gk;
static uint32_t FULL;
static int pw[64];
static int invE[MAXG];
static int perm[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t BUF1[MAXN], BUF2[MAXN], RC[MAXN], RN[MAXN];
static uint64_t rng_state = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_int(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
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

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk;
    int c = y / gk, e = y % gk;
    long aa = ((long)pw[b] * c + a) % gm;
    return (int)(aa * gk + (b + e) % gk);
}

static void setup_group(int k, int m, int k2, int r) {
    K = k;
    gm = m;
    gk = k2;
    G = m * k2;
    NV = 2 * K * G;
    FULL = (1u << (2 * K)) - 1u;
    int p = 1 % m;
    for (int t = 0; t < k2; t++) {
        pw[t] = p;
        p = (int)((long)p * r % m);
    }
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        int nb = (k2 - b) % k2;
        long na = ((long)m - ((long)pw[nb] * a) % m) % m;
        invE[x] = (int)(na * k2 + nb);
    }
}

static void sample_group(int target, int *pm, int *pk2, int *pr) {
    static const int K2[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int k2 = K2[rndint(20)];
    int m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1 && m > 2) {
        for (int t = 0; t < 60; t++) {
            int c = 2 + rndint(m - 2);
            if (gcd_int(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                break;
            }
        }
    }
    *pm = m;
    *pk2 = k2;
    *pr = r;
}

static void build_layer(int l) {
    int *row = nbr[l];
    for (int i = 0; i < K; i++) {
        int j = perm[l][i];
        int s = S[l][i];
        int si = invE[s];
        for (int g = 0; g < G; g++) row[i * G + g] = (K + j) * G + gmul(g, s);
        for (int h = 0; h < G; h++) row[(K + j) * G + h] = i * G + gmul(h, si);
    }
}

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) perm[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[l][i];
            perm[l][i] = perm[l][j];
            perm[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
        build_layer(l);
    }
}

static long dupcount(void) {
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 1; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (perm[l][i] == perm[l2][i] && S[l][i] == S[l2][i]) dup++;
    return dup;
}

/* Writes the reach mask of every vertex to res and returns the number of unreached pairs. */
static long eval_cost(uint32_t *res) {
    uint32_t *cur = BUF1, *nxt = BUF2, *tmp;
    for (int v = 0; v < NV; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] |= 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < NV; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < NV; v++) {
        bad += 2 * K - __builtin_popcount(cur[v]);
        res[v] = cur[v];
    }
    return bad;
}

static long full_cost(uint32_t *res) {
    return eval_cost(res) + PEN * dupcount();
}

static int anneal(long iters, long patience, double deadline) {
    random_state();
    uint32_t *Rc = RC, *Rn = RN, *tp;
    long cost = full_cost(Rc);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_c = cost, last_imp = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last_imp > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        int swapped = 0, l = 0, i = 0, i1 = 0, i2 = 0, old = 0;
        if (K >= 2 && rndint(100) < 25) {
            swapped = 1;
            l = rndint(d);
            i1 = rndint(K);
            i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = perm[l][i1];
            perm[l][i1] = perm[l][i2];
            perm[l][i2] = tmp;
            build_layer(l);
        } else {
            l = rndint(d);
            i = rndint(K);
            if (rndint(100) < 40) {
                int u = -1;
                for (int tries = 0; tries < 30 && u < 0; tries++) {
                    int v = rndint(NV);
                    if (Rc[v] != FULL) u = v;
                }
                if (u >= 0) {
                    int blk = u / G;
                    if (blk < K) {
                        i = blk;
                    } else {
                        for (int ii = 0; ii < K; ii++) {
                            if (perm[l][ii] == blk - K) {
                                i = ii;
                                break;
                            }
                        }
                    }
                }
            }
            old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            build_layer(l);
        }
        long nc = full_cost(Rn);
        if (nc <= cost || rnd01() < exp((double)(cost - nc) / temp)) {
            cost = nc;
            tp = Rc;
            Rc = Rn;
            Rn = tp;
            if (cost < best_c) {
                best_c = cost;
                last_imp = t;
            }
        } else {
            if (swapped) {
                int tmp = perm[l][i1];
                perm[l][i1] = perm[l][i2];
                perm[l][i2] = tmp;
            } else {
                S[l][i] = old;
            }
            build_layer(l);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit goal_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long goal = atol(argv[5]);
    double t_end = now() + limit * 0.92 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    long best_n = goal;
    int have = 0, bK = 1, bm = 2, bk2 = 1, br = 1;
    static int bperm[MAXD][MAXK], bS[MAXD][MAXK];
    double wins[KMAX + 1], trials[KMAX + 1];
    for (int k = 0; k <= KMAX; k++) {
        wins[k] = 0.0;
        trials[k] = 0.0;
    }
    double goalf = 1.05 * (double)best_n;
    if (goalf < 4.0) goalf = 4.0;

    while (now() < t_end) {
        int kc = 1;
        if (rndint(5) == 0) {
            kc = 1 + rndint(KMAX);
        } else {
            double bs = -1.0;
            for (int k = 1; k <= KMAX; k++) {
                double sc = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    kc = k;
                }
            }
        }
        int target = (int)(goalf / (2.0 * kc)) + rndint(3);
        if (target < 2) target = 2;
        int m, k2, r;
        sample_group(target, &m, &k2, &r);
        long nvl = 2L * kc * m * k2;
        if (nvl > MAXN) {
            goalf *= 0.9;
            if (goalf < 1.02 * (double)best_n) goalf = 1.02 * (double)best_n;
            continue;
        }
        if (nvl <= best_n) {
            if (goalf < 1.02 * (double)best_n) goalf = 1.02 * (double)best_n;
            continue;
        }
        setup_group(kc, m, k2, r);
        trials[kc] += 1.0;
        int ok = anneal(6000, 1500, t_end);
        if (ok) {
            wins[kc] += 1.0;
            if ((long)NV > best_n) {
                best_n = NV;
                have = 1;
                bK = K;
                bm = m;
                bk2 = k2;
                br = r;
                memcpy(bperm, perm, sizeof perm);
                memcpy(bS, S, sizeof S);
            }
            double f = 1.04 * (double)NV;
            if (goalf < f) goalf = f;
        } else {
            double f = 1.02 * (double)best_n;
            if (f < 0.99 * goalf) f = 0.99 * goalf;
            goalf = f;
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bK, bm, bk2, br);
    memcpy(perm, bperm, sizeof perm);
    memcpy(S, bS, sizeof S);
    for (int l = 0; l < d; l++) build_layer(l);
    if (full_cost(RC) != 0) {
        printf("0 0\n");
        return 0;
    }
    int half = K * G;
    printf("%d %ld\n", NV, (long)NV * d / 2);
    for (int v = 0; v < half; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nbr[l][v]);
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


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Phase 1: C bi-Cayley lift search over the remaining budget. It starts from the
    # current best order as its goal and only reports lifts that beat it.
    if d >= 3 and D >= 3:
        left = final - time.monotonic() - 1.0
        if left > 3.0:
            try:
                text = lib.run_c(C_LIFT, [d, D, int(seed) % 1000003, round(left, 2), best_n],
                                 timeout=left + 5.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
