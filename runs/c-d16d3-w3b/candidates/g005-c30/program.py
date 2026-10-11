import time

import lib


# ----------------------------------------------------------------------------
# Construction used here (D >= 3): bi-Cayley "Haar" graph over a finite abelian
# group G of order n with connection set S of size d.
#
#   A_g ~ B_h  iff  h - g in S          (2n vertices, every vertex has degree d)
#
# If S - S = G (every nonzero group element is a difference of two elements of S),
# then A-A and B-B pairs are at distance <= 2 and A-B pairs at distance <= 3,
# so the diameter is 3. The Moore-type limit gives n <= d^2 - d + 1, i.e. at most
# 2(d^2 - d + 1) vertices. For d = 16 that is 482 (the ceiling), and the record
# 394 = 2 * 197 corresponds to a difference covering of a group of order 197.
#
# The C engine searches, for n = nlo, nlo+1, ..., a set S containing 0 with
# S - S = G by simulated annealing on the number of uncovered nonzero elements.
# Groups tried for each n: the cyclic group Z_n first, then non-cyclic
# Z_a x Z_b (gcd(a, b) > 1). The engine stops at the first n that no group can
# cover within its slice of time and prints the largest success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXN 512

static int K, NG;
static int addt[MAXN][MAXN];
static int subt[MAXN][MAXN];
static int negt[MAXN];
static int cnt[MAXN];
static int unc[MAXN];
static int S[MAXK];
static int inS[MAXN];
static int cost;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int m) {
    return (int)((rnd64() >> 11) % (uint64_t)m);
}

static double urand(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Group Z_a x Z_b, element i*b + j. a = 1 gives the cyclic group Z_b. */
static void build_group(int a, int b) {
    NG = a * b;
    for (int y = 0; y < NG; y++) {
        int ni = (a - y / b) % a;
        int nj = (b - y % b) % b;
        negt[y] = ni * b + nj;
    }
    for (int x = 0; x < NG; x++) {
        for (int y = 0; y < NG; y++) {
            int i1 = x / b, j1 = x % b;
            int i2 = y / b, j2 = y % b;
            addt[x][y] = ((i1 + i2) % a) * b + (j1 + j2) % b;
        }
    }
    for (int x = 0; x < NG; x++)
        for (int y = 0; y < NG; y++)
            subt[x][y] = addt[x][negt[y]];
}

static void init_counts(void) {
    memset(cnt, 0, sizeof(int) * NG);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) cnt[subt[S[i]][S[j]]]++;
    cost = 0;
    for (int x = 1; x < NG; x++)
        if (cnt[x] == 0) cost++;
}

/* Remove (sign < 0) or add (sign > 0) the value val at position idx, against the other
   elements of S. Returns the change in the number of uncovered nonzero differences. */
static int apply_val(int idx, int val, int sign) {
    int delta = 0;
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        int t = S[j];
        int x = subt[val][t];
        int y = subt[t][val];
        if (sign < 0) {
            if (--cnt[x] == 0) delta++;
            if (--cnt[y] == 0) delta++;
        } else {
            if (cnt[x]++ == 0) delta--;
            if (cnt[y]++ == 0) delta--;
        }
    }
    return delta;
}

static int search(clock_t end) {
    for (;;) {
        if (clock() > end) return 0;
        memset(inS, 0, sizeof(int) * NG);
        S[0] = 0;
        inS[0] = 1;
        for (int k = 1; k < K; k++) {
            int v;
            do { v = rnd_int(NG); } while (inS[v]);
            S[k] = v;
            inS[v] = 1;
        }
        init_counts();
        double T = 0.3 + 0.4 * urand();
        int lbest = cost;
        long stag = 0;
        long limit = 20000L + 40L * NG;
        for (long it = 0; ; it++) {
            if (cost == 0) return 1;
            if ((it & 1023) == 0 && clock() > end) return 0;
            if (stag > limit) break;

            int i = 1 + rnd_int(K - 1);
            int v;
            if (urand() < 0.5) {
                int nu = 0;
                for (int x = 1; x < NG; x++)
                    if (cnt[x] == 0) unc[nu++] = x;
                int x = unc[rnd_int(nu)];
                int j = rnd_int(K);
                v = addt[x][S[j]];
            } else {
                v = rnd_int(NG);
            }
            if (inS[v]) { stag++; continue; }

            int old = S[i];
            int d1 = apply_val(i, old, -1);
            int d2 = apply_val(i, v, +1);
            int delta = d1 + d2;
            if (delta <= 0 || urand() < exp(-(double)delta / T)) {
                S[i] = v;
                inS[old] = 0;
                inS[v] = 1;
                cost += delta;
            } else {
                apply_val(i, v, -1);
                apply_val(i, old, +1);
            }
            if (cost < lbest) { lbest = cost; stag = 0; }
            else stag++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int nlo = atoi(argv[2]);
    int nmax = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    if (nmax > MAXN - 1) nmax = MAXN - 1;
    if (nlo < K) nlo = K;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd64();

    clock_t t0 = clock();
    int bestN = 0, bestA = 1, bestB = 1;
    int bestS[MAXK];

    for (int n = nlo; n <= nmax; n++) {
        int ga[4], gb[4], ng = 0;
        ga[ng] = 1; gb[ng] = n; ng++;
        for (int a = 2; a * a <= n && ng < 4; a++) {
            if (n % a == 0) {
                int b = n / a;
                if (gcd_i(a, b) > 1) { ga[ng] = a; gb[ng] = b; ng++; }
            }
        }
        int found = 0;
        for (int g = 0; g < ng && !found; g++) {
            double rem = budget - (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (rem < 0.02) break;
            double slice = rem * 0.3;
            clock_t end = clock() + (clock_t)(slice * CLOCKS_PER_SEC);
            build_group(ga[g], gb[g]);
            if (search(end)) {
                found = 1;
                bestN = n;
                bestA = ga[g];
                bestB = gb[g];
                memcpy(bestS, S, sizeof(int) * K);
            }
        }
        if (!found) break;
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    build_group(bestA, bestB);
    int n = NG;
    printf("%d %d\n", 2 * n, n * K);
    for (int g = 0; g < n; g++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", g, n + addt[g][bestS[j]]);
    return 0;
}
"""


def _largest_prime_power_le(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _fallback(d, D):
    """Safe valid graph: K_{d,d} (diameter 2) or the incidence graph of PG(2, q), q <= d-1 (diameter 3)."""
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])
    cands = [lib.haar_graph(d, range(d))]
    q = _largest_prime_power_le(d - 1)
    if q is not None and D >= 3:
        cands.append(lib.projective_plane_incidence(q))
    cands.sort(key=lambda g: -g[0])
    for g in cands:
        if lib.is_valid(g[0], g[1], d, D):
            return g
    return (1, [])


def build(d, D, seed, time_limit):
    best = _fallback(d, D)
    if D < 3 or d < 2 or d > 64:
        return best

    budget = 0.80 * time_limit - 1.0
    if budget < 0.5:
        return best

    nlo = d
    nmax = min(d * d - d + 1, 511)
    if nmax < nlo:
        return best

    try:
        out = lib.run_c(C_SOURCE, [d, nlo, nmax, seed % (2 ** 31), round(budget, 2)],
                        timeout=budget + 10.0)
        n2, e2 = lib.parse_graph_text(out)
        if n2 > best[0] and lib.is_valid(n2, e2, d, D):
            best = (n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
