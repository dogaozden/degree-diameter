"""Diameter-3 search via Haar graphs (bi-Cayley graphs over finite abelian groups).

Construction: for an abelian group G of order m and a d-subset S of G, join point x to
line y iff y - x is in S. This is bipartite and d-regular on 2m vertices. Two points x, x'
are at distance 2 iff x' - x is in S - S, and a point and a line are at distance <= 3
whenever S - S = G. So any S with S - S = G gives diameter 3 (valid for every D >= 3),
and m is at most d(d-1)+1, which is the Moore bound 2(d^2 - d + 1) for D = 3.

The C engine climbs m upward. For each m it picks a random abelian group Z_m1 x Z_m2
and runs simulated annealing on the number of uncovered nonzero differences. It keeps the
largest m for which a difference cover of size d is found. The construction is different
from the cyclic voltage lifts of the parent: the d = 16 target is a difference-cover search
over groups of order near 197 and above, where the record is 2*197 = 394.

Fallbacks: K_{d,d} (or K_2 for D = 1) is always checked with lib.is_valid. The
Araujo-Pardo/Lopez or projective-plane graph is used when it applies and is larger.
Only the best valid graph is returned. For D = 2 the graph is K_{d,d}, which is valid.
"""
import time

import lib

C_HAAR = r"""
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 512
#define MAXD 64
#define ITERS 300000L

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Group Z_M1 x Z_M2 with M = M1*M2; element x = a*M2 + b. */
static int M, M1, M2;
static int ADDT[MAXM * MAXM];
static int SUBT[MAXM * MAXM];

static int S[MAXD];
static int inS[MAXM];
static int cnt[MAXM];   /* cnt[x] = number of ordered pairs (s,t), s != t in S, with s - t = x */
static int cost;        /* number of nonzero x with cnt[x] == 0 */

static void set_group(int m, int m1) {
    M = m;
    M1 = m1;
    M2 = m / m1;
    for (int x = 0; x < M; x++) {
        int a1 = x / M2, b1 = x % M2;
        for (int y = 0; y < M; y++) {
            int a2 = y / M2, b2 = y % M2;
            ADDT[x * M + y] = ((a1 + a2) % M1) * M2 + (b1 + b2) % M2;
            SUBT[x * M + y] = ((a1 - a2 + M1) % M1) * M2 + (b1 - b2 + M2) % M2;
        }
    }
}

static void full_rebuild(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    memset(inS, 0, sizeof(int) * (size_t)M);
    for (int i = 0; i < d; i++) inS[S[i]] = 1;
    for (int i = 0; i < d; i++)
        for (int j = i + 1; j < d; j++) {
            cnt[SUBT[S[i] * M + S[j]]]++;
            cnt[SUBT[S[j] * M + S[i]]]++;
        }
    cost = 0;
    for (int x = 1; x < M; x++)
        if (cnt[x] == 0) cost++;
}

/* Remove S[i] from the cover counts (S[i] itself is left in place). */
static void del_elem(int i) {
    int v = S[i];
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int u = S[j];
        if (--cnt[SUBT[v * M + u]] == 0) cost++;
        if (--cnt[SUBT[u * M + v]] == 0) cost++;
    }
    inS[v] = 0;
}

/* Put w into slot i and add its differences to the cover counts. */
static void add_elem(int i, int w) {
    for (int j = 0; j < d; j++) {
        if (j == i) continue;
        int u = S[j];
        if (cnt[SUBT[w * M + u]]++ == 0) cost--;
        if (cnt[SUBT[u * M + w]]++ == 0) cost--;
    }
    S[i] = w;
    inS[w] = 1;
}

static void random_init(void) {
    for (int i = 0; i < d;) {
        int w = rndint(M), ok = 1;
        for (int j = 0; j < i; j++)
            if (S[j] == w) { ok = 0; break; }
        if (ok) S[i++] = w;
    }
    full_rebuild();
}

/* Returns 1 if a difference cover was found, 0 if the run ended without one, -1 on timeout. */
static int anneal(long iters, double T0, double T1) {
    double T = T0;
    for (long it = 0; it < iters; it++) {
        if (cost == 0) return 1;
        if ((it & 4095) == 0 && now() > t_end) return -1;
        if ((it & 255) == 0) T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = rndint(d);
        int w = rndint(M);
        if (inS[w]) continue;
        int v = S[i];
        int c0 = cost;
        del_elem(i);
        add_elem(i, w);
        int c1 = cost;
        if (c1 <= c0 || rnd01() < exp((double)(c0 - c1) / T)) continue;
        del_elem(i);
        add_elem(i, v);
    }
    return cost == 0 ? 1 : 0;
}

/* Try to find a difference cover of size d in a group of order m, restarting with random groups. */
static int attempt(int m, double until) {
    int divs[64], nd = 0;
    for (int a = 1; a <= m && nd < 64; a++)
        if (m % a == 0) divs[nd++] = a;
    while (now() < until) {
        set_group(m, divs[rndint(nd)]);
        random_init();
        int r = anneal(ITERS, 0.9, 0.08);
        if (r == 1) return 1;
        if (r == -1) return -1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + budget;

    if (d < 2 || D < 3 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    int mhi = d * (d - 1) + 1;   /* Moore bound: |S - S| <= d(d-1) + 1 */
    if (mhi > MAXM) mhi = MAXM;

    int best_m = 0, best_m1 = 1;
    int bestS[MAXD];
    for (int m = d + 1; m <= mhi; m++) {
        if (attempt(m, t_end) != 1) break;
        best_m = m;
        best_m1 = M1;
        memcpy(bestS, S, sizeof(int) * (size_t)d);
    }

    if (best_m == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(best_m, best_m1);
    printf("%d %ld\n", 2 * best_m, (long)best_m * d);
    for (int x = 0; x < best_m; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, best_m + ADDT[x * best_m + bestS[i]]);
    return 0;
}
"""


def _fallback(d, D):
    """K_{d,d} (diameter 2), or K_2 for D = 1. Always valid for the given d, D."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _known(d):
    """Projective-plane or Araujo-Pardo/Lopez graph for D = 3 when available, else None."""
    if d > 40:
        return None
    try:
        if lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)
    except Exception:
        return None
    return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found; roughly 80% of time_limit is used."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []

    best = None
    fb = _fallback(d, D)
    if lib.is_valid(fb[0], fb[1], d, D):
        best = fb

    def consider(g):
        nonlocal best
        if g is None:
            return
        try:
            n, e = g
            if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    consider(_known(d) if D == 3 else None)

    if D >= 3 and d >= 2:
        left = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
        if left > 1.0:
            try:
                text = lib.run_c(C_HAAR, [d, D, seed, f"{left:.2f}"], timeout=left + 4.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass

    if best is None:
        return 1, []
    return best
