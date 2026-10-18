"""Bi-Cayley voltage-lift search in C, then Python validation and exact small constructions.

C engine idea (new in this version):
  * Block-transitive cost. Left translation by a group element is an automorphism of a
    bi-Cayley lift, so "all pairs within distance D" reduces to "every vertex reaches all 2K
    block representatives within D steps". That is one bit-parallel pass over N vertices
    with 2K-bit masks, roughly 10-100x cheaper than Python.
  * Group sampler over all semidirect products Z_m x| Z_k2 with m*k2 = G near the target,
    for every divisor k2 <= 64 and every valid action r (r^k2 = 1 mod m, gcd(r, m) = 1).
  * Targeted moves: pick an unreached vertex and change the voltage of the layer that
    touches its block. Also swap block partners inside one layer.
  * Ratchet on the vertex goal (+4% on success, eased back on failure). Every success is
    re-verified by a full bitset distance check and a simplicity check before it is recorded.

Python handles exact constructions (projective planes, Araujo-Pardo-Lopez, generalized
quadrangle), calls the C engine once with most of the budget, and validates the result.
K_{d,d} is the fallback.
"""
import itertools
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

#define MAXN 12288
#define MAXDEG 16
#define MAXK 8
#define MAXK2 64
#define KMAX 6
#define PEN 6

static int DD, DIAM;
static uint64_t rs = 88172645463325252ULL;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* Semidirect group Z_gm x| Z_gk2, element a*gk2 + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gm, gk2, gG;
static int gpw[MAXK2];

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    int t = (int)(((long long)a + (long long)gpw[b] * c) % gm);
    int f = (b + e) % gk2;
    return t * gk2 + f;
}
static int ginv(int x) {
    int a = x / gk2, b = x % gk2;
    int nb = (gk2 - b) % gk2;
    long long na = ((long long)gm - ((long long)gpw[nb] * a) % gm) % gm;
    return (int)na * gk2 + nb;
}
static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}
static int powmod_i(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Random group with order in [Gmin, Gmin + spread). */
static int pick_group(int Gmin, int spread) {
    for (int att = 0; att < 200; att++) {
        int G = Gmin + rndi(spread);
        int divs[64], nd = 0;
        for (int q = 1; q <= MAXK2 && q <= G; q++)
            if (G % q == 0) divs[nd++] = q;
        if (nd == 0) continue;
        int k2 = (nd > 1 && rnd01() < 0.7) ? divs[1 + rndi(nd - 1)] : divs[0];
        int m = G / k2;
        int r = 0;
        if (m > 1) {
            int cnt = 0;
            r = -1;
            for (int c = 1; c < m; c++) {
                if (gcd_i(c, m) != 1) continue;
                if (powmod_i(c, k2, m) != 1) continue;
                cnt++;
                if (rndi(cnt) == 0) r = c;
            }
            if (r < 0) continue;
        }
        gm = m;
        gk2 = k2;
        gG = G;
        gpw[0] = 1 % m;
        for (int t = 1; t < k2; t++) gpw[t] = (int)((long long)gpw[t - 1] * r % m);
        return 1;
    }
    return 0;
}

/* Lift state. Blocks: A_i = [i*G, (i+1)*G), B_p = [(K+p)*G, (K+p+1)*G). */
static int K, G, NN, AN;
static int layers[MAXDEG][MAXK];
static int svol[MAXDEG][MAXK];
static int nbr[MAXDEG][MAXN];
static uint64_t bufA[MAXN], bufB[MAXN], curR[MAXN];
static uint64_t *lastR;

static int bestN = 0, bestAN = 0;
static int best_nbr[MAXDEG][MAXN];

/* Write layer l: A block i to B block p with voltage s (A_g ~ B_{g s}). */
static void set_dart(int l, int i, int p, int s) {
    layers[l][i] = p;
    svol[l][i] = s;
    int si = ginv(s);
    int ab = i * G, bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nbr[l][ab + g] = bb + gmul(g, s);
        nbr[l][bb + g] = ab + gmul(g, si);
    }
}

/* Unreached (vertex, representative) pairs. Final reach masks are left in lastR. */
static int evalReach(void) {
    int N = NN;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) cur[b * G] |= 1ULL << b;
    for (int r = 0; r < DIAM; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < DD; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    int unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - __builtin_popcountll(cur[v]);
    lastR = cur;
    return unr;
}

/* Number of duplicate edges (same block pair, same voltage, two layers). */
static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DD; l1++)
            for (int l2 = l1 + 1; l2 < DD; l2++)
                if (layers[l1][i] == layers[l2][i] && svol[l1][i] == svol[l2][i]) c++;
    return c;
}

static void record_best(void) {
    bestN = NN;
    bestAN = AN;
    for (int l = 0; l < DD; l++) memcpy(best_nbr[l], nbr[l], sizeof(int) * (size_t)NN);
}

/* Independent full verification: simple, bipartite, d-regular, diameter <= DIAM. */
static int full_check(void) {
    int N = NN, W = (N + 63) / 64;
    for (int v = 0; v < N; v++)
        for (int l1 = 0; l1 < DD; l1++) {
            int u = nbr[l1][v];
            if (u < 0 || u >= N || u == v || (v < AN) == (u < AN)) return 0;
            for (int l2 = 0; l2 < l1; l2++)
                if (nbr[l2][v] == u) return 0;
            int back = 0;
            for (int l2 = 0; l2 < DD && !back; l2++)
                if (nbr[l2][u] == v) back = 1;
            if (!back) return 0;
        }
    size_t sz = sizeof(uint64_t) * (size_t)N * (size_t)W;
    uint64_t *X = malloc(sz), *Y = malloc(sz);
    if (!X || !Y) {
        free(X);
        free(Y);
        return 0;
    }
    memset(X, 0, sz);
    for (int v = 0; v < N; v++) X[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = Y + (size_t)v * W;
            memcpy(dst, X + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int l = 0; l < DD; l++) {
                const uint64_t *s = X + (size_t)nbr[l][v] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = X;
        X = Y;
        Y = t;
    }
    long missing = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(X[(size_t)v * W + w]);
        missing += N - c;
    }
    free(X);
    free(Y);
    return missing == 0;
}

/* One annealing trial for the current group and K. Returns 1 on a verified success. */
static int run_trial(int iters, int patience, double sub_deadline) {
    uint64_t full = (1ULL << (2 * K)) - 1;
    for (int l = 0; l < DD; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1), t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) set_dart(l, i, perm[i], rndi(G));
    }
    int cost = evalReach() + PEN * dupcount();
    memcpy(curR, lastR, sizeof(uint64_t) * (size_t)NN);
    int bestc = cost, lastImp = 0;
    double c0 = cost > 1 ? (double)cost : 1.0;
    double T0 = 0.5 + 0.02 * c0;

#define ACCEPT(NC, T_)                                                   \
    do {                                                                 \
        cost = (NC);                                                     \
        memcpy(curR, lastR, sizeof(uint64_t) * (size_t)NN);              \
        if (cost < bestc) {                                              \
            bestc = cost;                                                \
            lastImp = t;                                                 \
        }                                                                \
    } while (0)

    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - lastImp > patience) break;
        if ((t & 31) == 0 && now_s() > sub_deadline) break;
        double T = T0 * (1.0 - (double)t / iters) + 0.3;

        if (K >= 2 && rnd01() < 0.2) {
            int l = rndi(DD);
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int p1 = layers[l][i1], p2 = layers[l][i2];
            int s1 = svol[l][i1], s2 = svol[l][i2];
            set_dart(l, i1, p2, s1);
            set_dart(l, i2, p1, s2);
            int nc = evalReach() + PEN * dupcount();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                ACCEPT(nc, T);
            } else {
                set_dart(l, i1, p1, s1);
                set_dart(l, i2, p2, s2);
            }
            continue;
        }

        int v = -1;
        if (rnd01() < 0.5) {
            for (int tr = 0; tr < 16; tr++) {
                int x = rndi(NN);
                if (curR[x] != full) {
                    v = x;
                    break;
                }
            }
        }
        int l, i;
        if (v >= 0) {
            l = rndi(DD);
            if (v < AN) {
                i = v / G;
            } else {
                int p = (v - AN) / G;
                i = 0;
                for (int j = 0; j < K; j++)
                    if (layers[l][j] == p) {
                        i = j;
                        break;
                    }
            }
        } else {
            l = rndi(DD);
            i = rndi(K);
        }
        int p = layers[l][i], old = svol[l][i];
        int ns = rndi(G);
        if (ns == old) continue;
        set_dart(l, i, p, ns);
        int nc = evalReach() + PEN * dupcount();
        if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
            ACCEPT(nc, T);
        } else {
            set_dart(l, i, p, old);
        }
    }
#undef ACCEPT

    if (cost != 0) return 0;
    if (!full_check()) return 0;
    if (NN > bestN) record_best();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [goal]\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long goal = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now_s();
    double tend = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }
    DD = d;
    DIAM = D;

    int trials[KMAX + 1] = {0}, wins[KMAX + 1] = {0};
    while (now_s() < tend) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndi(KMAX);
        } else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= KMAX; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) {
                    bs = sc;
                    k = c;
                }
            }
        }
        long Nt = goal > (long)bestN + 2 ? goal : (long)bestN + 2;
        if (Nt > MAXN) Nt = MAXN;
        int Gmin = (int)((Nt + 2 * k - 1) / (2 * k));
        if (Gmin < 1) Gmin = 1;
        int spread = Gmin / 25 + 2;
        if (2 * k * (Gmin + spread) > MAXN) spread = 0;
        if (2 * k * (Gmin + spread) > MAXN) continue;
        if (!pick_group(Gmin, spread)) continue;

        K = k;
        G = gG;
        AN = K * G;
        NN = 2 * AN;
        if (NN > MAXN || NN < 2) continue;

        trials[k]++;
        double now = now_s();
        double rem = tend - now;
        double sub = now + (rem * 0.25 > 3.0 ? rem * 0.25 : 3.0);
        if (sub > tend) sub = tend;
        if (run_trial(40000, 3000, sub)) {
            wins[k]++;
            goal = (long)(bestN * 1.04);
        } else {
            long fl = (long)(bestN * 1.01) + 2;
            double g2 = goal * 0.99;
            goal = (long)g2 > fl ? (long)g2 : fl;
        }
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", bestN, (long)bestAN * DD);
    for (int u = 0; u < bestAN; u++)
        for (int l = 0; l < DD; l++)
            printf("%d %d\n", u, best_nbr[l][u]);
    return 0;
}
'''


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 2.0)
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

    # Main phase: C bi-Cayley lift search, seeded with the current best size as its goal.
    remaining = final - time.monotonic() - 1.0
    if d >= 2 and D >= 2 and remaining > 3.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), int(best_n * 1.02) + 1],
                             timeout=remaining + 15.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
