import time

import lib


# ----------------------------------------------------------------------------
# C engine: cyclic Haar (bi-Cayley) graphs with a searched connection set.
#
# For m and a set S of d residues mod m, the Haar graph has vertices A_x and
# B_y (x, y in Z_m) with A_x ~ B_y iff y - x in S. It is d-regular and bipartite.
# The translation x -> x+c and the swap A_x <-> B_{-x} are automorphisms, so the
# diameter is at most D iff BFS from A_0 reaches all 2m vertices within D steps.
#
# For each m, from the largest candidate downward, simulated annealing searches S
# (0 always in S, WLOG) to maximise the number of vertices reached within D steps.
# The first m with full reach is printed. This is a different family from the
# projective-plane arc extensions: it is a cyclic difference-covering problem.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXDEG 64

static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double rnd01(void) {
    return (double)(rnd() & 0xFFFFFFu) / 16777216.0;
}

static double now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static int d, D, m;
static int S[MAXDEG];
static int dist[2 * MAXM];
static int que[2 * MAXM];

static int reach_count(void) {
    int N = 2 * m;
    for (int i = 0; i < N; i++) dist[i] = -1;
    int qh = 0, qt = 0, cnt = 1;
    dist[0] = 0;
    que[qt++] = 0;
    while (qh < qt) {
        int u = que[qh++];
        if (dist[u] >= D) continue;
        if (u < m) {
            for (int i = 0; i < d; i++) {
                int v = m + (u + S[i]) % m;
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    que[qt++] = v;
                    cnt++;
                }
            }
        } else {
            int y = u - m;
            for (int i = 0; i < d; i++) {
                int v = (y - S[i] + m) % m;
                if (dist[v] < 0) {
                    dist[v] = dist[u] + 1;
                    que[qt++] = v;
                    cnt++;
                }
            }
        }
    }
    return cnt;
}

/* Returns 1 if a set S with full reach was found (S left in place), else 0. */
static int anneal_slice(double seconds) {
    double t0 = now();
    int target = 2 * m;
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        int v, ok;
        do {
            v = 1 + (int)(rnd() % (uint32_t)(m - 1));
            ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == v) { ok = 0; break; }
        } while (!ok);
        S[i] = v;
    }
    int cur = reach_count();
    if (cur == target) return 1;
    while (1) {
        double el = now() - t0;
        if (el >= seconds) break;
        double frac = el / seconds;
        double T = 3.0 * (1.0 - frac) + 0.05;
        int i = 1 + (int)(rnd() % (uint32_t)(d - 1));
        int old = S[i];
        int v, ok;
        do {
            v = 1 + (int)(rnd() % (uint32_t)(m - 1));
            ok = 1;
            for (int j = 0; j < d; j++)
                if (S[j] == v) { ok = 0; break; }
        } while (!ok);
        S[i] = v;
        int c = reach_count();
        if (c >= cur || rnd01() < exp((double)(c - cur) / T)) {
            cur = c;
            if (cur == target) return 1;
        } else {
            S[i] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 8) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int mmax = atoi(argv[5]);
    int mmin = atoi(argv[6]);
    double slice = atof(argv[7]);

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    if (mmax > MAXM) mmax = MAXM;
    if (mmin < d + 1) mmin = d + 1;

    double t0 = now();
    for (m = mmax; m >= mmin; m--) {
        double rem = budget - (now() - t0);
        if (rem < 0.05) break;
        double sl = slice < rem ? slice : rem;
        if (anneal_slice(sl)) {
            int n = 2 * m;
            printf("%d %d\n", n, m * d);
            for (int x = 0; x < m; x++)
                for (int i = 0; i < d; i++)
                    printf("%d %d\n", x, m + (x + S[i]) % m);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()

    def left():
        return time_limit - (time.monotonic() - start)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return best

    if d < 2 or d > 64 or D < 2:
        return best

    budget = 0.75 * time_limit - 1.0
    if budget < 0.3:
        return best

    mmax = min(lib.moore_bound(d, D) // 2, 1024)
    mmin = max(d + 1, best[0] // 2 + 1)
    if mmax < mmin:
        return best

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), mmax, mmin, 0.5],
                        stdin_graph=None, timeout=max(1.0, 0.9 * time_limit))
        n, e = lib.parse_graph_text(out)
    except Exception:
        return best

    if n > best[0] and lib.is_valid(n, e, d, D):
        best = (n, e)
    return best
