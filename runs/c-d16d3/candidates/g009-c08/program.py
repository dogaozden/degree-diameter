"""Diameter-D bipartite search via cyclic Haar graphs (bold change from the arc-extension parent).

A Haar graph H(Z_m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for each s in S,
|S| = d. Translating indices by c is an automorphism, so the graph is valid for diameter D iff
every vertex is within distance D of a_0 and of b_0. The C engine searches for a connection set S
of d residues mod m by simulated annealing, minimising the number of unreached vertices from
a_0 and b_0. It climbs m upward and keeps the largest order that reaches zero cost. Python
checks everything with lib.is_valid and falls back to K_{d,d} (diameter 2) if needed.
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

#define MAXM 2048
#define MAXD 64
#define MAXV (2 * MAXM)

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int m;               /* current cyclic order */
static int S[MAXD];         /* connection set, residues mod m */
static int inS[MAXM];       /* membership flags for S */
static int vis[MAXV];
static int lev[MAXV];
static int qu[MAXV];
static int stamp = 0;

/* Number of vertices (out of 2m) NOT within distance D of src. */
static int unreached(int src) {
    int head = 0, tail = 0;
    stamp++;
    qu[tail++] = src;
    vis[src] = stamp;
    lev[src] = 0;
    while (head < tail) {
        int u = qu[head++];
        if (lev[u] >= D) continue;
        int nl = lev[u] + 1;
        if (u < m) {
            for (int k = 0; k < d; k++) {
                int v = m + (u + S[k]) % m;
                if (vis[v] != stamp) {
                    vis[v] = stamp;
                    lev[v] = nl;
                    qu[tail++] = v;
                }
            }
        } else {
            int j = u - m;
            for (int k = 0; k < d; k++) {
                int i = (j - S[k] + m) % m;
                if (vis[i] != stamp) {
                    vis[i] = stamp;
                    lev[i] = nl;
                    qu[tail++] = i;
                }
            }
        }
    }
    return 2 * m - tail;
}

/* Cost is zero iff the Haar graph H(Z_m, S) has diameter <= D. */
static int cost(void) { return unreached(0) + unreached(m); }

static void random_set(void) {
    for (int i = 0; i < m; i++) inS[i] = 0;
    for (int k = 0; k < d; k++) {
        int x;
        do {
            x = rndint(m);
        } while (inS[x]);
        inS[x] = 1;
        S[k] = x;
    }
}

/* Simulated annealing at fixed m. Returns 1 if a zero-cost S was found (left in S). */
static int search(long iters, double T0, double T1) {
    random_set();
    int cur = cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int k = rndint(d);
        int x;
        do {
            x = rndint(m);
        } while (inS[x]);
        int old = S[k];
        inS[old] = 0;
        inS[x] = 1;
        S[k] = x;
        int nc = cost();
        int delta = nc - cur;
        if (delta <= 0 || ((double)(rnd() % 1000000ULL) / 1000000.0) < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[k] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mstart = atoi(argv[5]);
    int mmax = atoi(argv[6]);

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1234567ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    if (mstart < d) mstart = d;

    double t_end = now() + budget;
    int bestm = 0;
    int bestS[MAXD];

    for (m = mstart; m <= mmax && now() < t_end; m++) {
        int ok = 0;
        if (m == d) {
            /* S must be all of Z_m: the graph is K_{d,d}, diameter 2. */
            for (int k = 0; k < d; k++) S[k] = k;
            ok = (cost() == 0);
        } else {
            for (int r = 0; r < 4 && now() < t_end && !ok; r++)
                ok = search(6000, 3.0, 0.3);
        }
        if (ok) {
            bestm = m;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
    }

    if (bestm == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestm, bestm * d);
    for (int i = 0; i < bestm; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, bestm + (i + bestS[k]) % bestm);
    return 0;
}
"""

MAX_M = 2047  # cap on the cyclic order, matching the C engine


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found; falls back to K_{d,d} (diameter 2)."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = None
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if lib.is_valid(fb_n, fb_e, d, D):
        best = (fb_n, fb_e)
    if best is None:
        return 1, []
    if time_limit < 2.0:
        return best

    moore = lib.moore_bound(d, D)
    mmax = min(moore // 2, MAX_M)  # a Haar graph on 2m vertices needs 2m <= moore
    if mmax < d:
        return best
    mstart = max(d, int(0.55 * mmax))

    budget = max(0.2, min(0.75 * time_limit, time_limit - 4.0))
    timeout = max(0.5, min(time_limit - 1.0, budget + 2.0))

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", mstart, mmax],
                         stdin_graph=None, timeout=timeout)
        n, edges = lib.parse_graph_text(text)
        if n > 1 and lib.is_valid(n, edges, d, D) and n > best[0]:
            best = (n, edges)
    except Exception:
        pass

    return best
