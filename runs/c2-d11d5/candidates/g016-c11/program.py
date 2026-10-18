"""Bi-Cayley lift search in C, with representative-only distance checks.

New idea: a semidirect product Z_m x| Z_k2 acts on every block of a bi-Cayley lift by
left translation, and that action is a graph automorphism. So all pairs are within
distance D exactly when every one of the 2k block representatives reaches all N
vertices within D steps. Each cost evaluation is therefore 2k truncated BFS runs over an
incrementally maintained neighbour table, not a full bitset closure.

The C engine samples (k, group, r), anneals the layer permutations and voltages with a
duplicate-edge penalty, and returns the largest lift it finds above the target size.
Python keeps exact constructions as fallback and checks every output with lib.is_valid.
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

#define MAXN 16384
#define MAXD 32
#define MAXG 8192
#define MAXK 4
#define MAXB 24
#define PEN 1000L
#define PAT 1500L

static int gd, gD;
static int kk, gm, gk, gG;
static int pw[MAXB];
static int ginv[MAXG];
static int sig[MAXD][MAXK];
static int Sv[MAXD][MAXK];
static int nbr[MAXN * MAXD];
static int best_nbr[MAXN * MAXD];
static int best_k, best_G, best_N, have_best;
static int distv[MAXN];
static int qu[MAXN];
static int mark[MAXK * MAXK * MAXG];
static int stampc;
static uint64_t rs = 88172645463325252ULL;
static double t_end;

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

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Semidirect product Z_gm x| Z_gk, element (a,b) coded a*gk+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / gk, b = x - a * gk;
    int c = y / gk, e = y - c * gk;
    int aa = (int)(((long)pw[b] * c + a) % gm);
    int bb = (b + e) % gk;
    return aa * gk + bb;
}

static int ginv_of(int x) {
    int a = x / gk, b = x - a * gk;
    int nb = (gk - b) % gk;
    int na = (int)((((long)(gm - a)) % gm) * pw[nb] % gm);
    return na * gk + nb;
}

static void setup_group(int m, int k2, int r) {
    gm = m;
    gk = k2;
    gG = m * k2;
    long p = 1 % m;
    for (int b = 0; b < gk; b++) {
        pw[b] = (int)p;
        p = p * r % m;
    }
    for (int x = 0; x < gG; x++) ginv[x] = ginv_of(x);
}

static int pick_r(int m, int k2) {
    if (k2 == 1 || m < 3) return 1 % m;
    if (rnd01() < 0.4) return 1;
    for (int t = 0; t < 400; t++) {
        int r = 2 + rndint(m - 2);
        if (gcd_i(r, m) == 1 && powmod_l(r, k2, m) == (long)(1 % m)) return r;
    }
    return 1;
}

/* Rewrite the neighbour entries touched by base vertex i in layer l (both sides). */
static void rebuild(int l, int i) {
    int p = sig[l][i];
    int s = Sv[l][i];
    int si = ginv[s];
    int A = i * gG;
    int B = (kk + p) * gG;
    for (int g = 0; g < gG; g++) {
        nbr[(A + g) * gd + l] = B + gmul(g, s);
        nbr[(B + g) * gd + l] = A + gmul(g, si);
    }
}

/* Cost = (block representative, vertex) pairs beyond distance D, plus duplicate penalty. */
static long full_cost(void) {
    long dup = 0;
    int N = 2 * kk * gG;
    stampc++;
    for (int l = 0; l < gd; l++)
        for (int i = 0; i < kk; i++) {
            int key = (i * MAXK + sig[l][i]) * gG + Sv[l][i];
            if (mark[key] == stampc) dup++;
            else mark[key] = stampc;
        }
    long unr = 0;
    for (int b = 0; b < 2 * kk; b++) {
        memset(distv, 0xff, sizeof(int) * (size_t)N);
        int head = 0, tail = 0;
        int src = b * gG;
        distv[src] = 0;
        qu[tail++] = src;
        while (head < tail) {
            int v = qu[head++];
            int dv = distv[v];
            if (dv >= gD) continue;
            const int *nb = nbr + v * gd;
            for (int l = 0; l < gd; l++) {
                int u = nb[l];
                if (distv[u] < 0) {
                    distv[u] = dv + 1;
                    qu[tail++] = u;
                }
            }
        }
        unr += N - tail;
    }
    return unr + PEN * dup;
}

static void random_lift(void) {
    for (int l = 0; l < gd; l++) {
        int perm[MAXK];
        for (int i = 0; i < kk; i++) perm[i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < kk; i++) {
            sig[l][i] = perm[i];
            Sv[l][i] = rndint(gG);
        }
    }
    for (int l = 0; l < gd; l++)
        for (int i = 0; i < kk; i++) rebuild(l, i);
}

/* Simulated annealing on permutations and voltages. Returns 1 when cost reaches 0. */
static int anneal(double deadline) {
    long cost = full_cost();
    long c0 = cost > 0 ? cost : 1;
    long best_cost = cost;
    long last = 0;
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 31) == 0 && now() > deadline) return 0;
        if (it - last > PAT) return 0;
        double frac = (double)(it - last) / (double)PAT;
        double T = 0.3 + 0.01 * (double)c0 * (1.0 - frac);
        long nc;
        int l = rndint(gd);
        if (kk >= 2 && rnd01() < 0.25) {
            int i1 = rndint(kk);
            int i2 = rndint(kk - 1);
            if (i2 >= i1) i2++;
            int tmp = sig[l][i1];
            sig[l][i1] = sig[l][i2];
            sig[l][i2] = tmp;
            rebuild(l, i1);
            rebuild(l, i2);
            nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                tmp = sig[l][i1];
                sig[l][i1] = sig[l][i2];
                sig[l][i2] = tmp;
                rebuild(l, i1);
                rebuild(l, i2);
            }
        } else {
            int i = rndint(kk);
            int old = Sv[l][i];
            int s = rndint(gG);
            if (s == old) continue;
            Sv[l][i] = s;
            rebuild(l, i);
            nc = full_cost();
            if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                cost = nc;
            } else {
                Sv[l][i] = old;
                rebuild(l, i);
            }
        }
        if (cost < best_cost) {
            best_cost = cost;
            last = it;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n]\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]);
    int Dd = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long target = argc > 5 ? atol(argv[5]) : 0;
    if (d < 2 || d > MAXD || Dd < 2) {
        printf("0 0\n");
        return 0;
    }
    gd = d;
    gD = Dd;
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static const int k2s[] = {1, 2, 2, 3, 4, 4, 5, 6, 8, 10, 12, 16, 20, 24};
    const int nk2 = (int)(sizeof(k2s) / sizeof(k2s[0]));

    long best_n = target;
    have_best = 0;
    while (now() < t_end) {
        kk = 1 + rndint(MAXK);
        long goal = best_n + 2;
        if (goal > MAXN) break;
        long Gmin = (goal + 2L * kk - 1) / (2L * kk);
        long Greq = Gmin + rndint((int)(Gmin / 40 + 3));
        int k2 = k2s[rndint(nk2)];
        long m = (Greq + k2 - 1) / k2;
        if (m < 2) m = 2;
        long G = m * k2;
        if (2L * kk * G > MAXN || G > MAXG) continue;
        int r = pick_r((int)m, k2);
        setup_group((int)m, k2, r);
        double remaining = t_end - now();
        double cap = remaining / 5.0 > 3.0 ? remaining / 5.0 : remaining;
        random_lift();
        if (anneal(now() + cap)) {
            long N = 2L * kk * G;
            if (N > best_n) {
                best_n = N;
                have_best = 1;
                best_k = kk;
                best_G = gG;
                best_N = (int)N;
                memcpy(best_nbr, nbr, sizeof(int) * (size_t)N * (size_t)gd);
            }
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long mE = (long)best_k * best_G * gd;
    printf("%d %ld\n", best_N, mE);
    for (int i = 0; i < best_k; i++)
        for (int g = 0; g < best_G; g++) {
            int v = i * best_G + g;
            for (int l = 0; l < gd; l++)
                printf("%d %d\n", v, best_nbr[v * gd + l]);
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

    # With D == 2 the bipartite optimum K_{d,d} is already in place.
    if D < 3:
        return best

    # C bi-Cayley lift search: it returns only lifts strictly larger than best_n.
    remaining = final - time.monotonic()
    if d >= 2 and remaining > 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2), best_n],
                             stdin_graph=None, timeout=remaining + 5)
            n_c, e_c = lib.parse_graph_text(text)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
