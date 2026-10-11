"""Cyclic Haar-graph search for bipartite graphs with max degree d and diameter D.

A Haar graph H(Z_m, S) has parts a_x and b_y (x, y in Z_m), joined by a_x ~ b_{x+s}
for s in S, |S| = d. It is d-regular, bipartite, and has 2m vertices. Vertex
translations are automorphisms, so diameter <= D only needs checking from a_0 and b_0.

The C engine finds a valid S for increasing m (simulated annealing on the number of
unreached vertices). Python keeps a projective-plane fallback and validates everything.
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

static int dd, DD;
static int mm;
static int *S, *bestS;
static char *inS;
static int *dist, *qu;
static uint64_t rs = 88172645463325252ULL;
static clock_t t_end;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

/* Number of vertices of the Haar graph NOT within distance DD of src. */
static int unreached(int src) {
    int N = 2 * mm;
    for (int i = 0; i < N; i++) dist[i] = -1;
    int head = 0, tail = 0;
    qu[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        int u = qu[head++];
        int du = dist[u];
        if (du >= DD) continue;
        if (u < mm) {
            for (int k = 0; k < dd; k++) {
                int t = u + S[k];
                if (t >= mm) t -= mm;
                int v = mm + t;
                if (dist[v] < 0) {
                    dist[v] = du + 1;
                    qu[tail++] = v;
                }
            }
        } else {
            int y = u - mm;
            for (int k = 0; k < dd; k++) {
                int t = y - S[k];
                if (t < 0) t += mm;
                if (dist[t] < 0) {
                    dist[t] = du + 1;
                    qu[tail++] = t;
                }
            }
        }
    }
    return N - tail;
}

/* Try to find a valid S for this m within a step budget. Returns 1 on success (S holds it). */
static int solve_m(int m, long budget) {
    mm = m;
    long done = 0;
    while (done < budget) {
        memset(inS, 0, (size_t)m);
        for (int k = 0; k < dd;) {
            int v = rndint(m);
            if (!inS[v]) {
                inS[v] = 1;
                S[k++] = v;
            }
        }
        int cur = unreached(0) + unreached(mm);
        if (cur == 0) return 1;
        long run = 0, runlen = 15000;
        while (run < runlen && done < budget) {
            double T = 1.5 * (1.0 - (double)run / (double)runlen) + 0.05;
            int idx = rndint(dd);
            int old = S[idx];
            int nv;
            do {
                nv = rndint(m);
            } while (inS[nv]);
            inS[old] = 0;
            inS[nv] = 1;
            S[idx] = nv;
            int c2 = unreached(0) + unreached(mm);
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
                if (cur == 0) return 1;
            } else {
                inS[nv] = 0;
                inS[old] = 1;
                S[idx] = old;
            }
            run++;
            done++;
            if ((done & 127) == 0 && clock() > t_end) return 0;
        }
        if (clock() > t_end) return 0;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time [m_lo]\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int m_lo = argc >= 6 ? atoi(argv[5]) : 0;

    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    t_end = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);

    if (dd < 2 || DD < 3) {
        printf("0 0\n");
        return 0;
    }

    /* Moore bound for bipartite graphs: 2 * sum_{i<D} (d-1)^i; Haar order is 2m. */
    double moore = 0.0, pw = 1.0;
    for (int i = 0; i < DD; i++) {
        moore += pw;
        pw *= (double)(dd - 1);
        if (moore > 1e9) break;
    }
    moore *= 2.0;
    long m_max_l = (long)(moore / 2.0);
    if (m_max_l > 200000) m_max_l = 200000;
    int m_max = (int)m_max_l;

    int m_start = m_lo > dd + 1 ? m_lo : dd + 1;
    if (m_start > m_max) {
        printf("0 0\n");
        return 0;
    }

    S = (int *)malloc(sizeof(int) * (size_t)dd);
    bestS = (int *)malloc(sizeof(int) * (size_t)dd);
    inS = (char *)calloc((size_t)m_max + 2, 1);
    dist = (int *)malloc(sizeof(int) * (size_t)(2 * m_max + 2));
    qu = (int *)malloc(sizeof(int) * (size_t)(2 * m_max + 2));
    if (!S || !bestS || !inS || !dist || !qu) {
        printf("0 0\n");
        return 0;
    }

    int best = 0;
    int m = m_start;
    long budget = 20000;
    int fails = 0;
    const int W = 6;

    while (m <= m_max && clock() < t_end) {
        if (solve_m(m, budget)) {
            best = m;
            memcpy(bestS, S, sizeof(int) * (size_t)dd);
            m++;
            fails = 0;
        } else {
            if (clock() >= t_end) break;
            m++;
            fails++;
            if (fails >= W) {
                m = best ? best + 1 : m_start;
                if (budget < 1000000000000L) budget *= 2;
                fails = 0;
            }
        }
    }

    if (best == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * best, best * dd);
    for (int x = 0; x < best; x++) {
        for (int k = 0; k < dd; k++) {
            int t = x + bestS[k];
            if (t >= best) t -= best;
            printf("%d %d\n", x, best + t);
        }
    }
    return 0;
}
"""


def _fallback(d, D):
    """Valid baseline: projective-plane incidence for D >= 3 when it fits, else K_{d,d}."""
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                if lib.is_valid(n, e, d, D):
                    return n, e
                break
    if D >= 2:
        return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]
    return 2, [(0, 1)]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]

    if D >= 3 and d >= 2:
        elapsed = time.monotonic() - t0
        budget = max(0.5, 0.75 * time_limit - elapsed - 1.0)
        timeout = max(1.0, 0.85 * time_limit - elapsed)
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", best[0] // 2 + 1],
                            timeout=timeout)
            n, edges = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
