import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts Z_m x| Z_k2 with k base
# blocks per side. Vertex (i, g) on side A is joined to (j, g*s) on side B for
# every layer l, where j = sig[l][i] and s = volt[l][i]. Left multiplication by
# the group is an automorphism, so the graph is checked with one BFS per base
# block (2k BFS in total), each limited to depth D. Cost is the number of
# vertices missing from those balls, and it is zero exactly when the lift has
# diameter <= D. Returns the first zero-cost lift it finds.
# ----------------------------------------------------------------------------

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

static int d, D, k, m, k2, r, G, N;
static int *pw, *sig, *volt, *isig, *ivolt, *nbr, *vis, *dep, *qu;
static int stamp = 0;

/* Element a*k2+b of Z_m x| Z_k2, product (a,b)(c,e) = (a + r^b c, b+e). */
static int mulg(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    int aa = (int)(((long long)a + (long long)pw[b] * c) % m);
    return aa * k2 + (b + e) % k2;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int invg(int x) {
    int a = x / k2, b = x % k2;
    int nb = (k2 - b) % k2;
    long long t = ((long long)pw[nb] * a) % m;
    int c = (int)((m - t) % m);
    return c * k2 + nb;
}

static void randomize(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) sig[l * k + i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = sig[l * k + i]; sig[l * k + i] = sig[l * k + j]; sig[l * k + j] = t;
        }
        for (int i = 0; i < k; i++) volt[l * k + i] = rint_(G);
    }
}

static void build_nbr(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            isig[l * k + sig[l * k + i]] = i;
            ivolt[l * k + i] = invg(volt[l * k + i]);
        }
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++)
                nbr[v * d + l] = (k + sig[l * k + i]) * G + mulg(g, volt[l * k + i]);
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = isig[l * k + j];
                nbr[v * d + l] = i * G + mulg(h, ivolt[l * k + i]);
            }
        }
}

/* Sum over the 2k representatives of the number of vertices outside the depth-D ball. */
static long long cost_fn(void) {
    build_nbr();
    long long total = 0;
    if (stamp >= 0x7ffffff0) { memset(vis, 0, sizeof(int) * (size_t)N); stamp = 0; }
    for (int s = 0; s < 2 * k; s++) {
        int src = s * G;
        int h = 0, t = 0;
        stamp++;
        qu[t++] = src; vis[src] = stamp; dep[src] = 0;
        while (h < t) {
            int v = qu[h++];
            if (dep[v] >= D) continue;
            for (int l = 0; l < d; l++) {
                int w = nbr[v * d + l];
                if (vis[w] != stamp) {
                    vis[w] = stamp; dep[w] = dep[v] + 1; qu[t++] = w;
                }
            }
        }
        total += N - t;
    }
    return total;
}

static void output(void) {
    build_nbr();
    int A = k * G;
    int *tmp = malloc(sizeof(int) * (size_t)d);
    int *eu = malloc(sizeof(int) * (size_t)N * d);
    int *ev = malloc(sizeof(int) * (size_t)N * d);
    int cnt = 0;
    for (int v = 0; v < A; v++) {
        for (int l = 0; l < d; l++) tmp[l] = nbr[v * d + l];
        for (int a = 1; a < d; a++) {
            int x = tmp[a], b = a - 1;
            while (b >= 0 && tmp[b] > x) { tmp[b + 1] = tmp[b]; b--; }
            tmp[b + 1] = x;
        }
        for (int l = 0; l < d; l++) {
            if (l > 0 && tmp[l] == tmp[l - 1]) continue;
            eu[cnt] = v; ev[cnt] = tmp[l]; cnt++;
        }
    }
    printf("%d %d\n", N, cnt);
    for (int e = 0; e < cnt; e++) printf("%d %d\n", eu[e], ev[e]);
    free(tmp); free(eu); free(ev);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double limit = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    r = atoi(argv[8]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    if (d < 1 || D < 1 || k < 1 || k > 8 || m < 1 || k2 < 1) { printf("0 0\n"); return 0; }
    G = m * k2;
    N = 2 * k * G;
    if (N > 400000) { printf("0 0\n"); return 0; }
    r %= m;
    pw = malloc(sizeof(int) * (size_t)k2);
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    if ((long long)pw[k2 - 1] * r % m != 1 % m) { printf("0 0\n"); return 0; }

    sig = malloc(sizeof(int) * (size_t)k * d);
    volt = malloc(sizeof(int) * (size_t)k * d);
    isig = malloc(sizeof(int) * (size_t)k * d);
    ivolt = malloc(sizeof(int) * (size_t)k * d);
    nbr = malloc(sizeof(int) * (size_t)N * d);
    vis = calloc((size_t)N, sizeof(int));
    dep = malloc(sizeof(int) * (size_t)N);
    qu = malloc(sizeof(int) * (size_t)N);

    const double T0 = 12.0, T1 = 0.3;
    const long long PATIENCE = 20000;
    clock_t c0 = clock();
    randomize();
    long long cur = cost_fn();
    long long bestc = cur, last = 0, it = 0;
    double T = T0, el = 0.0;

    while (cur != 0) {
        if ((it & 127) == 0) {
            el = (double)(clock() - c0) / CLOCKS_PER_SEC;
            if (el >= limit) break;
            double frac = el / limit;
            T = T0 * pow(T1 / T0, frac);
        }
        it++;
        if (it - last > PATIENCE) {
            randomize();
            cur = cost_fn();
            bestc = cur;
            last = it;
            continue;
        }

        int kind = 0, l = 0, i = 0, i2 = 0, oldv = 0;
        if (k >= 2 && rdbl() < 0.3) {
            kind = 1;
            l = rint_(d); i = rint_(k); i2 = rint_(k - 1);
            if (i2 >= i) i2++;
            int t = sig[l * k + i]; sig[l * k + i] = sig[l * k + i2]; sig[l * k + i2] = t;
        } else {
            l = rint_(d); i = rint_(k);
            oldv = volt[l * k + i];
            volt[l * k + i] = rint_(G);
        }

        long long nc = cost_fn();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur < bestc) { bestc = cur; last = it; }
        } else {
            if (kind == 1) {
                int t = sig[l * k + i]; sig[l * k + i] = sig[l * k + i2]; sig[l * k + i2] = t;
            } else {
                volt[l * k + i] = oldv;
            }
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    output();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _run_c(d, D, k, m, k2, r, seed, seconds):
    """One annealing run for a fixed base size and group; returns (n, edges), with n = 0 on failure."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{seconds:.2f}", k, m, k2, r],
                    stdin_graph=None, timeout=seconds + 4.0)
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

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    deadline = t0 + 0.9 * time_limit - 2.0
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    failures = 0

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        base = best[0] // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 16 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        if 2 * k * G <= best[0]:
            continue
        seconds = min(remaining - 0.5, max(2.0, 0.1 * time_limit))
        if seconds < 1.0:
            break
        trials[k] += 1
        try:
            n, e = _run_c(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), seconds)
            failures = 0
        except Exception:
            failures += 1
            continue
        if n > 0:
            before = best[0]
            consider(n, e)
            if best[0] > before:
                wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
