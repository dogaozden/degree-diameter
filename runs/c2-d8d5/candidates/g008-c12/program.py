import math
import random
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

/* Bi-Cayley lifts over the semidirect product Z_M2 x| Z_K2 (element a*K2+b,
   (a,b)(c,e) = (a + R^b c, b+e)). Base has k blocks per side. Layer l is a
   perfect matching between side-0 block i and side-1 block P[l][i], with
   voltage S[l][i]: (i,g) ~ (k+j, g*s). The group acts regularly on each
   block, so the distance check only needs one BFS per block. */

static int d, D, k, G, N, M2, K2, R;
static int *Mt, *Inv, *pw, *P, *S, *nb, *stamp, *qu, *Psave, *Ssave;
static int curStamp = 0;
#define DUPW 4
#define PATIENCE 3000

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int aa = (int)(((long long)a + (long long)pw[b] * c) % M2);
    int bb = (b + e) % K2;
    return aa * K2 + bb;
}

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) P[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l * k + i]; P[l * k + i] = P[l * k + j]; P[l * k + j] = t;
        }
        for (int i = 0; i < k; i++) S[l * k + i] = rint_(G);
    }
}

static void build_nb(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = P[l * k + i], s = S[l * k + i], is = Inv[s];
            for (int g = 0; g < G; g++)
                nb[(i * G + g) * d + l] = (k + j) * G + Mt[g * G + s];
            for (int h = 0; h < G; h++)
                nb[((k + j) * G + h) * d + l] = i * G + Mt[h * G + is];
        }
    }
}

/* Total unreached ordered pairs from one representative per block. Zero iff valid. */
static long long eval_cost(void) {
    long long total = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G;
        curStamp++;
        int t = 0, ls = 0, le = 1;
        qu[t++] = src;
        stamp[src] = curStamp;
        for (int dep = 0; dep < D; dep++) {
            if (ls == le) break;
            for (int q = ls; q < le; q++) {
                int v = qu[q];
                const int *row = nb + (size_t)v * d;
                for (int l = 0; l < d; l++) {
                    int u = row[l];
                    if (stamp[u] != curStamp) { stamp[u] = curStamp; qu[t++] = u; }
                }
            }
            ls = le;
            le = t;
        }
        total += N - t;
    }
    return total;
}

static long long dup_count(void) {
    long long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1 * k + i] == P[l2 * k + i] && S[l1 * k + i] == S[l2 * k + i]) c++;
    return c;
}

static void output_graph(void) {
    int kg = k * G;
    printf("%d %d\n", 2 * kg, kg * d);
    for (int v = 0; v < kg; v++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", v, nb[v * d + l]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    M2 = atoi(argv[5]);
    K2 = atoi(argv[6]);
    R = atoi(argv[7]);
    k = atoi(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d < 1 || D < 1 || k < 1 || M2 < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    G = M2 * K2;
    if (G < 2 || G > 2500 || 2LL * k * G > 6000) { printf("0 0\n"); return 0; }
    N = 2 * k * G;
    R = R % M2;
    if (gcd_(R, M2) != 1) { printf("0 0\n"); return 0; }

    pw = malloc(sizeof(int) * K2);
    pw[0] = 1 % M2;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long long)pw[b - 1] * R % M2);
    if ((long long)pw[K2 - 1] * R % M2 != 1 % M2) { printf("0 0\n"); return 0; }

    Mt = malloc(sizeof(int) * (size_t)G * G);
    Inv = malloc(sizeof(int) * G);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            Mt[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        int found = -1;
        for (int y = 0; y < G; y++)
            if (Mt[x * G + y] == 0) { found = y; break; }
        if (found < 0) { printf("0 0\n"); return 0; }
        Inv[x] = found;
    }

    nb = malloc(sizeof(int) * (size_t)N * d);
    stamp = calloc(N, sizeof(int));
    qu = malloc(sizeof(int) * N);
    P = malloc(sizeof(int) * d * k);
    S = malloc(sizeof(int) * d * k);
    Psave = malloc(sizeof(int) * d * k);
    Ssave = malloc(sizeof(int) * d * k);
    if (!nb || !stamp || !qu || !P || !S || !Psave || !Ssave) { printf("0 0\n"); return 0; }

    clock_t c0 = clock();
    init_random();
    build_nb();
    long long cur = eval_cost() + DUPW * dup_count();
    if (cur == 0) { output_graph(); return 0; }
    long long bestc = cur;
    long long since = 0;

    const double T0 = 3.0, T1 = 0.05;
    while (1) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double frac = el / limit;
        double T = T0 * pow(T1 / T0, frac);

        memcpy(Psave, P, sizeof(int) * d * k);
        memcpy(Ssave, S, sizeof(int) * d * k);
        if (k >= 2 && rdbl() < 0.3) {
            int l = rint_(d);
            int i1 = rint_(k);
            int i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int t = P[l * k + i1]; P[l * k + i1] = P[l * k + i2]; P[l * k + i2] = t;
        } else {
            int l = rint_(d);
            int i = rint_(k);
            S[l * k + i] = rint_(G);
        }
        build_nb();
        long long nc = eval_cost() + DUPW * dup_count();
        if (nc <= cur || rdbl() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) { output_graph(); return 0; }
            if (cur < bestc) { bestc = cur; since = 0; } else since++;
        } else {
            memcpy(P, Psave, sizeof(int) * d * k);
            memcpy(S, Ssave, sizeof(int) * d * k);
            since++;
        }
        if (since > PATIENCE) {
            init_random();
            build_nb();
            cur = eval_cost() + DUPW * dup_count();
            bestc = cur;
            since = 0;
            if (cur == 0) { output_graph(); return 0; }
        }
    }
    printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group_for(G, rng):
    """Return (m, k2, r) with a group Z_m x| Z_k2 of order G = m*k2, or None."""
    divs = [k2 for k2 in range(1, G + 1) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs[:8]:
        m = G // k2
        if k2 == 1:
            return m, 1, 1
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return m, k2, rng.choice(rs)
    return None


def _run_group(d, D, seed, seconds, m, k2, r, k):
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", m, k2, r, k],
                    stdin_graph=None, timeout=seconds + 15.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Exact constructions for D = 3 (calibration case returns immediately).
    if D == 3:
        if lib.is_prime_power(d - 1):
            return best
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Bi-Cayley search over non-cyclic groups, searched in C. Each call aims for
    # an order just above the current best.
    search_end = t0 + time_limit - 5.0
    failures = 0
    while True:
        remaining = search_end - time.monotonic()
        if remaining < 1.0 or failures >= 3:
            break
        k = rng.choice((1, 1, 2, 2, 3, 4))
        G = best[0] // (2 * k) + 1 + rng.choice((0, 0, 0, 1, 2))
        if G < 2 or G > 2500 or 2 * k * G > 6000:
            continue
        grp = _group_for(G, rng)
        if grp is None:
            continue
        m, k2, r = grp
        slice_s = min(remaining, 6.0)
        try:
            n2, e2 = _run_group(d, D, rng.randrange(1, 1 << 30), slice_s, m, k2, r, k)
        except Exception:
            failures += 1
            continue
        if n2 > best[0]:
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
