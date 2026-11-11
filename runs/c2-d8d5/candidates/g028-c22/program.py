import time

import lib


# ----------------------------------------------------------------------------
# C engine: Haar-graph annealer over semidirect groups Z_m x| Z_k.
#
# Haar graph H(G, S): left vertices g, right vertices G+h, edge (g, G + g*s)
# for s in S, |S| = d. Left translations act transitively on each side, so the
# diameter is at most D iff the eccentricity of left identity and of right
# identity are both at most D. The cost is the number of vertices not reached
# within D steps from those two sources. Simulated annealing toggles one
# element of S at a time. The largest group order that reaches cost 0 is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 2600
#define MAXN2 (2 * MAXG)

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int dd, DD, G;
static int *mul, *inv;
static int *vis, stamp;
static int *fa, *fb;

static const int KS[] = {1, 1, 1, 2, 2, 2, 3, 4, 5, 6, 8, 10, 12};
#define NK 13

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static long long powmod(long long b, int e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int find_r(int m, int k) {
    if (k == 1 || m < 3) return 1;
    for (int t = 0; t < 600; t++) {
        int c = 1 + rint_(m - 1);
        if (gcd_(c, m) == 1 && powmod(c, k, m) == 1) return c;
    }
    return 1;
}

/* Multiplication table of Z_m x| Z_k: (a,b)*(c,e) = (a + r^b c, b + e), element a*k+b. */
static void build_group(int m, int k, int r) {
    G = m * k;
    int pw[64];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) inv[x] = -1;
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        int *row = mul + (size_t)x * G;
        for (int y = 0; y < G; y++) {
            int c = y / k, e = y % k;
            int a2 = (int)((a + (long long)pw[b] * c) % m);
            int b2 = (b + e) % k;
            row[y] = a2 * k + b2;
            if (row[y] == 0) inv[x] = y;
        }
    }
}

static int in_set(int x, const int *S, int n) {
    for (int i = 0; i < n; i++) if (S[i] == x) return 1;
    return 0;
}

/* Number of vertices reached from src within DD steps (src in [0, 2G)). */
static int reach(int src, const int *S) {
    stamp++;
    int cnt = 1;
    vis[src] = stamp;
    int *cur = fa, *nxt = fb;
    int nf = 1;
    cur[0] = src;
    int N2 = 2 * G;
    for (int lvl = 0; lvl < DD && cnt < N2 && nf > 0; lvl++) {
        int nn = 0;
        for (int i = 0; i < nf; i++) {
            int u = cur[i];
            if (u < G) {
                const int *row = mul + (size_t)u * G;
                for (int j = 0; j < dd; j++) {
                    int v = G + row[S[j]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; cnt++; }
                }
            } else {
                int h = u - G;
                const int *row = mul + (size_t)h * G;
                for (int j = 0; j < dd; j++) {
                    int v = row[inv[S[j]]];
                    if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; cnt++; }
                }
            }
        }
        int *t = cur; cur = nxt; nxt = t;
        nf = nn;
    }
    return cnt;
}

static int cost_of(const int *S) {
    return (2 * G - reach(0, S)) + (2 * G - reach(G, S));
}

static int anneal(int *S, int iters, double end) {
    int cost = cost_of(S);
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 63) == 0 && cpu() > end) break;
        double T = 2.0 * pow(0.025, (double)it / iters);
        int j = rint_(dd);
        int old = S[j], nw;
        do { nw = rint_(G); } while (in_set(nw, S, dd));
        S[j] = nw;
        int c2 = cost_of(S);
        int delta = c2 - cost;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = c2;
        else S[j] = old;
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double total = atof(argv[4]);
    int init = argc > 5 ? atoi(argv[5]) : dd + 1;
    if (dd < 1 || DD < 1 || dd > 60) { printf("0 0\n"); return 0; }

    mul = malloc(sizeof(int) * (size_t)MAXG * MAXG);
    inv = malloc(sizeof(int) * MAXG);
    vis = calloc(MAXN2, sizeof(int));
    fa = malloc(sizeof(int) * MAXN2);
    fb = malloc(sizeof(int) * MAXN2);
    int *S = malloc(sizeof(int) * dd);
    int *bu = malloc(sizeof(int) * (size_t)MAXG * dd);
    int *bv = malloc(sizeof(int) * (size_t)MAXG * dd);
    if (!mul || !inv || !vis || !fa || !fb || !S || !bu || !bv) { printf("0 0\n"); return 0; }

    int bestG = 0, bestM = 0;
    double start = cpu(), limit = start + total;
    double cap = total / 6.0;
    if (cap < 2.0) cap = 2.0;

    while (1) {
        double tn = cpu();
        if (tn >= limit - 0.02) break;

        int want = bestG > 0 ? bestG + 1 + rint_(1 + bestG / 200) : init;
        if (want < dd + 1) want = dd + 1;
        int k = KS[rint_(NK)];
        int m = (want + k - 1) / k + rint_(3);
        if (m < 2) m = 2;
        if ((long long)m * k > MAXG) continue;
        int r = find_r(m, k);
        build_group(m, k, r);
        if (G < dd + 1) continue;

        for (int j = 0; j < dd; j++) {
            int nw;
            do { nw = rint_(G); } while (in_set(nw, S, j));
            S[j] = nw;
        }
        double end = tn + cap;
        if (end > limit) end = limit;
        int c = anneal(S, 60000, end);
        if (c == 0 && G > bestG) {
            bestG = G;
            bestM = 0;
            for (int g = 0; g < G; g++) {
                for (int j = 0; j < dd; j++) {
                    bu[bestM] = g;
                    bv[bestM] = G + mul[(size_t)g * G + S[j]];
                    bestM++;
                }
            }
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestG, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bu[i], bv[i]);
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

    # Main phase: C annealer over Haar graphs of semidirect groups.
    budget = time_limit - (time.monotonic() - t0) - 6.0
    if budget >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", max(d + 1, best[0] // 2)],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
