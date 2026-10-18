import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Python glue: exact baselines (projective plane, generalized quadrangle),
# then the C engine, which runs a bi-Cayley lift search over semidirect
# products Z_m x| Z_k2 starting from the best graph found so far.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine.
#
# New in this version: the whole bi-Cayley annealing search runs in C with
# implicit semidirect-product arithmetic (no G x G tables), wall-clock budget,
# a bandit over base sizes k, and iterated local search with restarts from the
# best state. The C side gets roughly 10-50x more reach evaluations per second
# than the Python version, so the time budget buys much deeper search.
#
# Model: base vertices A_i (i < K) and B_j (j < K); group G = Z_m x| Z_k2 with
# elements a*k2+b and (a,b)(c,e) = (a + r^b c, b + e). Layer l joins A_i to B_{lay[l][i]}
# with voltage S[l][i]: A_{i,g} ~ B_{j, g*s}. Each layer is a permutation, so
# every vertex has degree d. Bipartite by construction. Validity is checked by
# bitmask reach from the block representatives (left multiplication is an
# automorphism) plus a duplicate-dart penalty.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000LL
#define KICK 3
#define MAXRESTART 3
#define MAXK 4

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static const int KLIST[20] = {1,1,2,2,3,4,5,6,7,8,9,10,12,14,16,18,20,24,30,36};
static int PC[256];

static int d_, D_, K, M, K2, G, N;
static int Rp[64];

static int *nbr;      /* nbr[l*N + v] */
static int *lay;      /* lay[l*K + i] = B-block of A-block i in layer l */
static int *Sv;       /* Sv[l*K + i]  = voltage */
static int *blay, *bS;
static uint32_t *curR, *candR, *scrT;

static long long pmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)Rp[b] * c + a) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)Rp[nb] * a) % M;
    t = (M - t) % M;
    return (int)(t * K2 + nb);
}

static void setup_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    G = m * k2;
    Rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) Rp[b] = (int)((long long)Rp[b - 1] * r % m);
}

static int sample_group(int target, int *om, int *ok2, int *orr) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = KLIST[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (gcd_i(r, m) != 1 || pmod(r, 2, m) != 1 % m) continue;
        } else if (m <= 2) {
            r = 1;
        } else {
            r = -1;
            for (int t = 0; t < 60; t++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && pmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        *om = m;
        *ok2 = k2;
        *orr = r;
        return 1;
    }
    return 0;
}

static void set_dart(int l, int i) {
    int j = lay[l * K + i], s = Sv[l * K + i];
    int *row = nbr + (size_t)l * N;
    int sinv = ginv(s);
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (K + j) * G + gmul(g, s);
        row[(K + j) * G + g] = i * G + gmul(g, sinv);
    }
}

static void rebuild_all(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);
}

static int dupcount(void) {
    int dK = d_ * K, c = 0;
    for (int a = 0; a < dK; a++) {
        for (int b = 0; b < a; b++) {
            if (a % K == b % K && lay[a] == lay[b] && Sv[a] == Sv[b]) {
                c++;
                break;
            }
        }
    }
    return c;
}

/* Writes per-vertex reach bitmasks into out; returns number of unreached (block, vertex) pairs. */
static long long eval_reach(uint32_t *out) {
    uint32_t *cur = out, *nxt = scrT;
    memset(out, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] |= (1u << b);
    for (int st = 0; st < D_; st++) {
        int ch = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d_; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) ch = 1;
        }
        uint32_t *tp = cur;
        cur = nxt;
        nxt = tp;
        if (!ch) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint32_t) * (size_t)N);
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - PC[out[v] & 255];
    return unr;
}

static int anneal(int iters, int patience, double deadline) {
    int dK = d_ * K;
    int perm[MAXK];
    uint32_t full = (1u << (2 * K)) - 1u;

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
    }
    for (int a = 0; a < dK; a++) Sv[a] = rndint(G);
    rebuild_all();

    long long cost = eval_reach(curR) + PEN * dupcount();
    double c0 = cost > 1 ? (double)cost : 1.0;
    long long bestc = cost;
    memcpy(blay, lay, sizeof(int) * dK);
    memcpy(bS, Sv, sizeof(int) * dK);
    int last = 0, restarts = 0;

    for (int t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 31) == 0 && now() > deadline) break;

        if (t - last > patience) {
            if (++restarts > MAXRESTART) break;
            memcpy(lay, blay, sizeof(int) * dK);
            memcpy(Sv, bS, sizeof(int) * dK);
            rebuild_all();
            for (int q = 0; q < KICK; q++) {
                int l = rndint(d_), i = rndint(K);
                Sv[l * K + i] = rndint(G);
                set_dart(l, i);
            }
            cost = eval_reach(curR) + PEN * dupcount();
            last = t;
            continue;
        }

        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        double x = rnd01();

        if (K >= 2 && x < 0.25) {
            /* Layer-swap move: exchange the B-targets of two A-blocks in one layer. */
            int l = rndint(d_);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int p1 = l * K + i1, p2 = l * K + i2;
            int tmp = lay[p1];
            lay[p1] = lay[p2];
            lay[p2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long long c2 = eval_reach(candR) + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                uint32_t *tp = curR;
                curR = candR;
                candR = tp;
                if (cost < bestc) {
                    bestc = cost;
                    last = t;
                    memcpy(blay, lay, sizeof(int) * dK);
                    memcpy(bS, Sv, sizeof(int) * dK);
                }
            } else {
                tmp = lay[p1];
                lay[p1] = lay[p2];
                lay[p2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1, v = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int c = rndint(N);
                if (curR[c] != full) {
                    v = c;
                    break;
                }
            }
        }
        if (v >= 0) {
            int block = v / G;
            l = rndint(d_);
            if (block < K) {
                i = block;
            } else {
                int jj = block - K;
                for (int q = 0; q < K; q++)
                    if (lay[l * K + q] == jj) {
                        i = q;
                        break;
                    }
            }
        } else {
            l = rndint(d_);
            i = rndint(K);
        }
        if (i < 0) continue;

        int p = l * K + i;
        int old = Sv[p];
        int nw = rndint(G);
        if (nw == old) continue;
        Sv[p] = nw;
        set_dart(l, i);
        long long c2 = eval_reach(candR) + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            uint32_t *tp = curR;
            curR = candR;
            candR = tp;
            if (cost < bestc) {
                bestc = cost;
                last = t;
                memcpy(blay, lay, sizeof(int) * dK);
                memcpy(bS, Sv, sizeof(int) * dK);
            }
        } else {
            Sv[p] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void extract_edges(int *eu, int *ev) {
    int c = 0;
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d_; l++) {
            eu[c] = u;
            ev[c] = nbr[(size_t)l * N + u];
            c++;
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        PC[x] = c;
    }

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) {
        sn = 0;
        sm = 0;
    }
    if (sm < 0) sm = 0;
    int *su = malloc(sizeof(int) * (sm + 1));
    int *sv = malloc(sizeof(int) * (sm + 1));
    int cnt = 0;
    for (int e = 0; e < sm; e++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        su[cnt] = a;
        sv[cnt] = b;
        cnt++;
    }

    int bestN = sn, bestM = cnt;
    int *bu = su, *bv = sv;
    double deadline = now() + tl;

    if (d_ >= 2 && D_ >= 3) {
        int trials[MAXK + 1], wins[MAXK + 1];
        for (int k = 0; k <= MAXK; k++) {
            trials[k] = 0;
            wins[k] = 0;
        }
        while (now() < deadline) {
            int k;
            if (rnd01() < 0.2) {
                k = 1 + rndint(MAXK);
            } else {
                double bv_ = -1.0;
                k = 1;
                for (int kk = 1; kk <= MAXK; kk++) {
                    double val = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                    if (val > bv_) {
                        bv_ = val;
                        k = kk;
                    }
                }
            }
            K = k;
            int base = bestN / (2 * k);
            int extra = base / 8 + 1;
            if (extra < 2) extra = 2;
            int target = base + 1 + rndint(extra);
            if (target < 2) target = 2;

            int m, k2, r;
            if (!sample_group(target, &m, &k2, &r)) continue;
            setup_group(m, k2, r);
            if (2 * K * G <= bestN) continue;
            N = 2 * K * G;

            nbr = malloc(sizeof(int) * (size_t)d_ * N);
            lay = malloc(sizeof(int) * (size_t)d_ * K);
            Sv = malloc(sizeof(int) * (size_t)d_ * K);
            blay = malloc(sizeof(int) * (size_t)d_ * K);
            bS = malloc(sizeof(int) * (size_t)d_ * K);
            curR = malloc(sizeof(uint32_t) * (size_t)N);
            candR = malloc(sizeof(uint32_t) * (size_t)N);
            scrT = malloc(sizeof(uint32_t) * (size_t)N);

            trials[k]++;
            int ok = anneal(40000, 4000, deadline);
            if (ok) {
                wins[k]++;
                int *eu = malloc(sizeof(int) * (size_t)d_ * K * G);
                int *ev = malloc(sizeof(int) * (size_t)d_ * K * G);
                extract_edges(eu, ev);
                bestN = N;
                bestM = d_ * K * G;
                bu = eu;
                bv = ev;
            }

            free(nbr);
            free(lay);
            free(Sv);
            free(blay);
            free(bS);
            free(curR);
            free(candR);
            free(scrT);
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bu[e], bv[e]);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C search from the best start graph. Budget leaves room for compilation
    # and the final validity check.
    elapsed = time.monotonic() - t0
    budget = min(0.85 * time_limit, time_limit - 7.0) - elapsed
    if d >= 2 and D >= 3 and budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}"],
                            stdin_graph=best, timeout=budget + 6.0)
            n2, e2 = lib.parse_graph_text(out)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
