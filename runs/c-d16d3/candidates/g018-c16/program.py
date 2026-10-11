"""Cyclic Haar-graph search for diameter-D bipartite graphs.

Construction: the Haar graph H(m, S) has vertices a_i and b_i for i in Z_m, with a_i adjacent to
b_{i+s} for each s in S, |S| = d. It is d-regular and bipartite. Translations of Z_m together
with the side-swap a_i -> b_{-i}, b_j -> a_{-j} make it vertex-transitive, so its diameter equals
the eccentricity of a_0, one BFS. C searches for S by simulated annealing, minimising the number
of vertices farther than D from a_0, and tries m upward from d until the search stalls.
Haar graphs with S - S = Z_m give diameter 3 with 2m vertices, so the search targets 2m > 394.
The fallback is K_{d,d}, which is checked with lib.is_valid.
"""
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXD 64

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd() >> 11) / 9007199254740992.0; }

static double cpu(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int distv[2 * MAXM];
static int qu[2 * MAXM];

/* Number of vertices at distance > D from a_0 in H(m,S).
   The graph is vertex-transitive, so this is zero iff the diameter is <= D. */
static int bad_count(int m, int d, int D, const int *S) {
    for (int i = 0; i < 2 * m; i++) distv[i] = -1;
    int h = 0, t = 0;
    distv[0] = 0;
    qu[t++] = 0;
    while (h < t) {
        int u = qu[h++];
        if (distv[u] >= D) continue;
        for (int k = 0; k < d; k++) {
            int v;
            if (u < m) {
                v = m + (u + S[k]) % m;
            } else {
                int j = u - m;
                v = ((j - S[k]) % m + m) % m;
            }
            if (distv[v] < 0) {
                distv[v] = distv[u] + 1;
                qu[t++] = v;
            }
        }
    }
    int bad = 0;
    for (int i = 0; i < 2 * m; i++)
        if (distv[i] < 0) bad++;
    return bad;
}

static int inset(const int *S, int cnt, int x) {
    for (int k = 0; k < cnt; k++)
        if (S[k] == x) return 1;
    return 0;
}

/* Simulated annealing over S (0 fixed in S) for fixed m > d. Returns 1 and fills outS on success. */
static int try_m(int m, int d, int D, double deadline, int *outS) {
    int S[MAXD];
    const int ITER = 4000;
    while (cpu() < deadline) {
        S[0] = 0;
        for (int k = 1; k < d; k++) {
            int x;
            do {
                x = 1 + rndint(m - 1);
            } while (inset(S, k, x));
            S[k] = x;
        }
        int cur = bad_count(m, d, D, S);
        const double T0 = 3.0;
        for (int it = 0; it < ITER && cur > 0; it++) {
            double T = T0 * (1.0 - (double)it / ITER) + 0.05;
            int k = 1 + rndint(d - 1);
            int x;
            do {
                x = 1 + rndint(m - 1);
            } while (inset(S, d, x));
            int old = S[k];
            S[k] = x;
            int nb = bad_count(m, d, D, S);
            int delta = nb - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
                cur = nb;
            } else {
                S[k] = old;
            }
        }
        if (cur == 0) {
            memcpy(outS, S, sizeof(int) * d);
            return 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double t_end = cpu() + budget;
    int bestm = 0;
    int bestS[MAXD];
    int fails = 0;
    for (int m = d; m < MAXM && cpu() < t_end; m++) {
        int S[MAXD];
        int ok;
        if (m == d) {
            for (int k = 0; k < d; k++) S[k] = k;   /* K_{d,d} */
            ok = (bad_count(m, d, D, S) == 0);
        } else {
            double per = t_end - cpu();
            if (per > 2.0) per = 2.0;
            ok = try_m(m, d, D, cpu() + per, S);
        }
        if (ok) {
            bestm = m;
            memcpy(bestS, S, sizeof(int) * d);
            fails = 0;
        } else if (++fails >= 6) {
            break;
        }
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    int m = bestm;
    printf("%d %d\n", 2 * m, m * d);
    for (int i = 0; i < m; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, m + (i + bestS[k]) % m);
    return 0;
}
"""


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found; K_{d,d} is the safe fallback."""
    if d < 1:
        return 1, []
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else (1, [])
    if d < 2 or D < 2:
        return best

    budget = max(1.0, 0.85 * time_limit - 3.0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                         stdin_graph=None, timeout=time_limit * 0.92)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
