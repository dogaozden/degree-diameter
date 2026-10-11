"""Cyclic lift search (a different construction from the parent's semidirect lifts).

Python builds the cheap starts (K_{d,d}, the cycle for d = 2, PG(2,q), Araujo-Pardo-Lopez) and
validates them with lib.is_valid. The C engine then searches bipartite voltage lifts over the
cyclic group Z_N with base multigraphs on P <= 3 vertices per side. Every base vertex has degree d,
and each dart is a distinct triple (i, j, g), so the lift is simple and d-regular. The diameter is
checked by BFS from the 2P fibre representatives only, since translations are automorphisms.
Hill-climbing on the voltages drives the count of pairs at distance > D to zero. Python keeps the
best valid graph and falls back to the starts whenever C returns nothing.
"""
import time

import lib

C_SOURCE = r'''
/* Cyclic bipartite lift search.
 * Usage: prog d D seed time_limit LB
 * Searches for a valid d-regular bipartite lift over Z_N with 2*P*N > LB vertices.
 * Output: "n m" plus edges of the best lift found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXP 3
#define MAXND (MAXP * MAXD)

static int d, D;
static long moore, best_n;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Current lift state. Dart t joins A-fibre dA[t] to B-fibre dB[t] with voltage dG[t]. */
static int P, N, nd;
static int dA[MAXND], dB[MAXND], dG[MAXND];
static int nv;
static int adj[MAXN][MAXD];
static int cnt[MAXN];
static int distv[MAXN], stampv[MAXN], queue_buf[MAXN];
static int stamp = 0;

/* Best valid lift found so far. */
static int bP, bN, bnd;
static int bdA[MAXND], bdB[MAXND], bdG[MAXND];
static int have = 0;

/* True if giving dart t voltage g repeats an existing (i, j, g) triple. */
static int clash(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && dA[s] == dA[t] && dB[s] == dB[t] && dG[s] == g) return 1;
    return 0;
}

static void build(void) {
    nv = 2 * P * N;
    for (int v = 0; v < nv; v++) cnt[v] = 0;
    for (int t = 0; t < nd; t++) {
        int a0 = dA[t] * N, b0 = (P + dB[t]) * N, g = dG[t];
        for (int x = 0; x < N; x++) {
            int u = a0 + x, w = b0 + (x + g) % N;
            adj[u][cnt[u]++] = w;
            adj[w][cnt[w]++] = u;
        }
    }
}

/* Sum over the 2P representatives b*N of the number of vertices not within distance D.
 * Zero exactly when the lift has diameter <= D (translations are automorphisms). */
static long bad_count(void) {
    long total = 0;
    for (int b = 0; b < 2 * P; b++) {
        int src = b * N;
        stamp++;
        int head = 0, tail = 0;
        stampv[src] = stamp;
        distv[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (distv[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = adj[v][i];
                if (stampv[u] != stamp) {
                    stampv[u] = stamp;
                    distv[u] = distv[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static void save_best(void) {
    bP = P;
    bN = N;
    bnd = nd;
    for (int t = 0; t < nd; t++) {
        bdA[t] = dA[t];
        bdB[t] = dB[t];
        bdG[t] = dG[t];
    }
    have = 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit LB\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    best_n = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = moore_bound();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    while (now() < t_end) {
        long nmin1 = best_n / 2 + 1;
        if (nmin1 < d) nmin1 = d;
        if (2 * nmin1 > moore || 2 * nmin1 > MAXN) break;

        int r = rndint(10);
        int p = r < 5 ? 1 : (r < 8 ? 2 : 3);
        long nmin = best_n / (2L * p) + 1;
        if (nmin < d) nmin = d;
        long Nl = nmin + (rndint(4) == 0 ? rndint(3) : 0);
        if (2L * p * Nl > moore || 2L * p * Nl > MAXN) continue;

        P = p;
        N = (int)Nl;
        nd = P * d;

        /* Random base: d permutations of P points, dart k*P+i joins A_i to B_perm_k(i). */
        for (int k = 0; k < d; k++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < P; i++) {
                int t = k * P + i;
                dA[t] = i;
                dB[t] = perm[i];
            }
        }
        for (int t = 0; t < nd; t++) dG[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clash(t, g));
            dG[t] = g;
        }

        build();
        long cur = bad_count();
        int steps = 30000;
        for (int s = 0; s < steps && cur > 0; s++) {
            if ((s & 127) == 0 && now() > t_end) break;
            int t = rndint(nd);
            int old = dG[t];
            int g = old, tries = 0;
            do {
                g = rndint(N);
                tries++;
            } while ((g == old || clash(t, g)) && tries < 100);
            if (g == old || clash(t, g)) continue;
            dG[t] = g;
            build();
            long nb = bad_count();
            if (nb <= cur || rnd01() < 0.01) {
                cur = nb;
            } else {
                dG[t] = old;
                build();
            }
        }
        if (cur == 0 && 2L * P * N > best_n) {
            best_n = 2L * P * N;
            save_best();
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int n = 2 * bP * bN;
    long m = (long)bnd * bN;
    printf("%d %ld\n", n, m);
    for (int t = 0; t < bnd; t++) {
        int a0 = bdA[t] * bN, b0 = (bP + bdB[t]) * bN, g = bdG[t];
        for (int x = 0; x < bN; x++)
            printf("%d %d\n", a0 + x, b0 + (x + g) % bN);
    }
    return 0;
}
'''


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty). Each is checked again by the caller."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 3), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
