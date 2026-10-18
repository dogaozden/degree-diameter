"""Bold variant: bi-Cayley / voltage-lift search with transitive BFS checking.

Lifts of a d-regular base multigraph (p vertices per side) over a semidirect product
Z_m x| Z_k are vertex-transitive on each fibre (left translation by the group is an
automorphism). So diameter <= D holds iff a BFS from A_{i,e} and from B_{j,e} reaches
everything within D. Each check is O(p^2 N d) rather than the O(n^2 D / 64) bitset
check, so the C engine can test many groups and voltage sets per second.
Search: pick N just above the current best, sample a random group and base, then
anneal over voltages using the count of (source, vertex) pairs farther than D.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 8192
#define MAXD 16
#define MAXP 3
#define MAXG 8192
#define MAXDART 64

typedef struct { int i, j, g; } Dart;
typedef struct { int m, k, r; int rp[MAXG]; } Grp;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k: element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r; found = 1;
            }
        }
    }
    if (!found) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* ------------------------------------------------------------ base graph */

/* Random connected d-regular bipartite base multigraph with p vertices per side. */
static int make_base(int p, int M[MAXP][MAXP]) {
    for (int tries = 0; tries < 2000; tries++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ voltages */

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* ------------------------------------------------------------ lift evaluation */

static int adjv[MAXV][MAXD];
static int degv[MAXV];
static int dist_[MAXV];
static int qq[MAXV];

static void build_adj(int p, int N, const Grp *G, const Dart *dt, int nd) {
    int V = 2 * p * N;
    for (int v = 0; v < V; v++) degv[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = p * N + dt[t].j * N + gmul(G, x, dt[t].g);
            adjv[a][degv[a]++] = b;
            adjv[b][degv[b]++] = a;
        }
}

/* Left translations are automorphisms fixing each fibre, so BFS from A_{i,e} and B_{j,e}
 * decides the diameter. Returns the number of (source, vertex) pairs at distance > D. */
static long deficiency(int p, int N) {
    int V = 2 * p * N;
    long bad = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s < p ? s * N : p * N + (s - p) * N;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int h = 0, tl = 0, reached = 1;
        dist_[src] = 0;
        qq[tl++] = src;
        while (h < tl) {
            int v = qq[h++];
            if (dist_[v] >= D) continue;
            for (int k = 0; k < degv[v]; k++) {
                int u = adjv[v][k];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    qq[tl++] = u;
                    reached++;
                }
            }
        }
        bad += V - reached;
    }
    return bad;
}

/* ------------------------------------------------------------ best store */

static int bestType = 0;          /* 0 = complete bipartite fallback, 1 = lift */
static long bestV = 0;
static int bestP, bestN, bestNd;
static Grp bestG;
static Dart bestDt[MAXDART];

/* Anneal voltages of one random lift. On success store it as the best. */
static int attempt(int p, int N, const Grp *G, int M[MAXP][MAXP], long steps) {
    Dart dt[MAXDART];
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? rndint(N) : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_adj(p, N, G, dt, nd);
    long cur = deficiency(p, N);
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_adj(p, N, G, dt, nd);
        long nb = deficiency(p, N);
        double T = 1.2 * (1.0 - (double)s / (double)steps) + 0.05;
        if (nb <= cur || rnd01() < exp(-(double)(nb - cur) / T)) cur = nb;
        else dt[t].g = old;
    }
    if (cur != 0) return 0;
    bestType = 1;
    bestV = 2L * p * N;
    bestP = p;
    bestN = N;
    bestNd = nd;
    bestG = *G;
    memcpy(bestDt, dt, sizeof(Dart) * nd);
    return 1;
}

static void print_best(void) {
    if (bestType == 0 || D < 2) {
        if (D < 2) {
            printf("2 1\n0 1\n");
            return;
        }
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
        return;
    }
    int p = bestP, N = bestN, V = 2 * p * N;
    long m = (long)bestNd * N;
    printf("%d %ld\n", V, m);
    for (int t = 0; t < bestNd; t++)
        for (int x = 0; x < N; x++) {
            int a = bestDt[t].i * N + x;
            int b = p * N + bestDt[t].j * N + gmul(&bestG, x, bestDt[t].g);
            printf("%d %d\n", a, b);
        }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { print_best(); return 0; }

    long moore = moore_bound();
    long cap = moore < MAXV ? moore : MAXV;
    bestV = 2L * d;
    long stepN = 1;
    static Grp G;
    int M[MAXP][MAXP];

    while (D >= 2 && now() < t_end) {
        int r = rndint(10);
        int p = r < 5 ? 1 : (r < 8 ? 2 : 3);
        if (p > 1 && (d < 2 || 2L * p * (bestV / (2 * p) + 1) > cap)) p = 1;
        long Nmin = bestV / (2 * p) + 1;
        if (2L * p * Nmin > cap) break;
        long N = Nmin + rndint((int)stepN);
        if (N < d) N = d;
        if (2L * p * N > cap) N = cap / (2 * p);
        if (N < d || N < Nmin) continue;
        if (!random_group((int)N, &G)) continue;
        if (!make_base(p, M)) continue;
        long V = 2L * p * N;
        long steps = 3000 + 20000000L / (V * d);
        if (attempt(p, (int)N, &G, M, steps)) {
            stepN = stepN * 2 > 64 ? 64 : stepN * 2;
        } else {
            stepN = stepN / 2 < 1 ? 1 : stepN / 2;
        }
    }
    print_best();
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if best[0] >= lib.moore_bound(d, D):
        budget = min(budget, 0.5)   # nothing beats a Moore graph; just exercise the C engine
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             stdin_graph=start, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(*out, d, D):
                best = out
        except Exception:
            pass   # keep the valid fallback
    return best
