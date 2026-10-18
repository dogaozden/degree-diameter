"""Voltage lifts over semidirect groups Z_M x|_r Z_K for the bipartite degree-diameter problem.

Construction: take a small bipartite base multigraph with K vertices on each side,
each of degree d. Each dart from A_i to B_j carries a voltage g in a finite group G of
order N = M*K. The lift has vertices (base, x) for x in G, with (A_i, x) joined to
(B_j, x*g) for every dart (i, j, g). Left multiplication is an automorphism, so the
lift has diameter <= D iff every base vertex at the identity reaches all 2KN vertices
within D steps. The search is simulated annealing over the dart voltages and the
endpoints of the darts, with the cost equal to the number of unreached pairs.

Earlier versions searched only K = 1 (Haar graphs). This version also tries K = 2..6
base vertices per side, which gives a larger order 2KN for the same group order N.

Groups are semidirect products Z_M x|_r Z_K, which include cyclic groups and,
for prime q, the affine groups F_q x| H. Candidates are climbed in ascending order of
total order T = 2KN, starting above a Moore-fraction floor and above the current best.
Each success restarts the climb just above the new best. A valid K_{d,d}, a projective
plane incidence graph, or the Araujo-Pardo-Lopez graph is kept as a fallback. Every
returned graph passes lib.is_valid.
"""
import itertools
import math
import random
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

/* Usage: prog d D seed time_limit K GM GK r
 * Group G = Z_GM x|_r Z_GK, element a*GK+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Stdin is ignored. Output "n m" and edges of a valid lift, or "0 0". */

#define MAXK 8
#define MAXD 32
#define MAXNG 2600

static int d, D, K, GM, GK, N, NV;
static int PW[MAXNG];
static int *MUL, *INVG, *vis, *que;
static int stamp = 0;
static int dB[MAXK * MAXD], dG[MAXK * MAXD];
static int bl[MAXK][MAXD];
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul_el(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)a + (long)PW[b] * c) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

/* Darts of B_j, used for the B-side neighbourhoods. */
static void build_bl(void) {
    int cnt[MAXK];
    for (int j = 0; j < K; j++) cnt[j] = 0;
    for (int t = 0; t < K * d; t++) {
        int j = dB[t];
        bl[j][cnt[j]++] = t;
    }
}

/* 1 if dart t duplicates another dart: same A vertex, same B vertex, same voltage. */
static int dup_with(int t) {
    int tot = K * d, A = t / d;
    for (int s = 0; s < tot; s++) {
        if (s == t) continue;
        if (s / d == A && dB[s] == dB[t] && dG[s] == dG[t]) return 1;
    }
    return 0;
}

/* Number of lift vertices within distance D of the source id. */
static int reach_count(int src) {
    stamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int base = v / N, x = v - base * N;
            const int *row = MUL + (long)x * N;
            if (base < K) {
                for (int e = 0; e < d; e++) {
                    int t = base * d + e;
                    int u = (K + dB[t]) * N + row[dG[t]];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            } else {
                int j = base - K;
                for (int e = 0; e < d; e++) {
                    int t = bl[j][e];
                    int u = (t / d) * N + row[INVG[dG[t]]];
                    if (vis[u] != stamp) { vis[u] = stamp; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Sum over base vertices (at the identity) of unreached lift vertices. */
static long total_cost(void) {
    long c = 0;
    for (int s = 0; s < 2 * K; s++) c += (long)(NV - reach_count(s * N));
    return c;
}

static int init_random(void) {
    int tot = K * d;
    for (int attempt = 0; attempt < 100; attempt++) {
        int slots[MAXK * MAXD];
        int t = 0;
        for (int j = 0; j < K; j++)
            for (int e = 0; e < d; e++) slots[t++] = j;
        for (int i = tot - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = slots[i];
            slots[i] = slots[r];
            slots[r] = tmp;
        }
        for (int q = 0; q < tot; q++) {
            dB[q] = slots[q];
            dG[q] = rndint(N);
        }
        int ok = 0;
        for (int rep = 0; rep < 2000 && !ok; rep++) {
            ok = 1;
            for (int q = 0; q < tot; q++)
                if (dup_with(q)) {
                    dG[q] = rndint(N);
                    ok = 0;
                }
        }
        if (ok) {
            build_bl();
            return 1;
        }
    }
    return 0;
}

/* One annealing run from a random valid start. Returns 1 when cost 0 is reached. */
static int anneal(double until, long iters) {
    if (!init_random()) return 0;
    long c = total_cost();
    if (c == 0) return 1;
    int tot = K * d;
    double Ts = 0.03 * (double)c + 1.0, Te = 0.2;
    for (long it = 0; it < iters; it++) {
        if ((it & 63) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / (double)iters);
        if (rndint(2) == 0) {
            int t = rndint(tot);
            int old = dG[t];
            int ng = rndint(N);
            if (ng == old) continue;
            dG[t] = ng;
            if (dup_with(t)) { dG[t] = old; continue; }
            long c2 = total_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else dG[t] = old;
        } else {
            int t1 = rndint(tot), t2 = rndint(tot);
            if (dB[t1] == dB[t2]) continue;
            int tmp = dB[t1];
            dB[t1] = dB[t2];
            dB[t2] = tmp;
            if (dup_with(t1) || dup_with(t2)) {
                tmp = dB[t1];
                dB[t1] = dB[t2];
                dB[t2] = tmp;
                continue;
            }
            build_bl();
            long c2 = total_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) {
                c = c2;
            } else {
                tmp = dB[t1];
                dB[t1] = dB[t2];
                dB[t2] = tmp;
                build_bl();
            }
        }
        if (c == 0) return 1;
    }
    return c == 0;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    double t_start = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    K = atoi(argv[5]);
    GM = atoi(argv[6]);
    GK = atoi(argv[7]);
    long r = atol(argv[8]);
    double t_end = t_start + limit * 0.93 - 0.2;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2 || K < 1 || K > MAXK || GM < 1 || GK < 1) {
        printf("0 0\n");
        return 0;
    }
    N = GM * GK;
    if (N < d || N > MAXNG) {
        printf("0 0\n");
        return 0;
    }
    r %= GM;
    PW[0] = 1 % GM;
    for (int b = 1; b < GK; b++) PW[b] = (int)(((long)PW[b - 1] * r) % GM);
    if (((long)PW[GK - 1] * r) % GM != 1 % GM) {
        printf("0 0\n");
        return 0;
    }

    MUL = malloc(sizeof(int) * (size_t)N * (size_t)N);
    INVG = malloc(sizeof(int) * (size_t)N);
    NV = 2 * K * N;
    vis = calloc((size_t)NV, sizeof(int));
    que = malloc(sizeof(int) * (size_t)NV);
    if (!MUL || !INVG || !vis || !que) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MUL[x * N + y] = gmul_el(x, y);
    for (int x = 0; x < N; x++) {
        INVG[x] = 0;
        for (int y = 0; y < N; y++)
            if (MUL[x * N + y] == 0) { INVG[x] = y; break; }
    }

    int found = 0;
    while (now() < t_end) {
        if (anneal(t_end, 20000)) { found = 1; break; }
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", NV, K * d * N);
    for (int i = 0; i < K; i++)
        for (int x = 0; x < N; x++)
            for (int e = 0; e < d; e++) {
                int t = i * d + e;
                int u = i * N + x;
                int v = (K + dB[t]) * N + MUL[x * N + dG[t]];
                printf("%d %d\n", u, v);
            }
    return 0;
}
'''

MAX_GROUP = 2600
MAX_K = 6


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N, seed):
    """Up to two (m, k, r) descriptors of Z_m x|_r Z_k with m*k = N, nonabelian when possible."""
    nonab = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                nonab.append((m, k, r))
    random.Random(seed * 1000003 + N).shuffle(nonab)
    return nonab[:2] if nonab else [(N, 1, 1)]


def _candidates(d, T0, mb, seed, cache):
    """Yield (T, K, m, k, r) with T = 2*K*(m*k) >= T0, in ascending T."""
    for T in range(T0, mb + 1):
        for K in (2, 3, 4, 1, 5, MAX_K):
            if T % (2 * K):
                continue
            N = T // (2 * K)
            if N < d or N > MAX_GROUP:
                continue
            if N not in cache:
                cache[N] = _groups(N, seed)
            for m, k, r in cache[N]:
                yield T, K, m, k, r


def _climb(d, D, seed, deadline, best, mb):
    """Ascending search over (K, group) candidates above the current best graph."""
    cache = {}
    tried = set()

    def fresh(start):
        return _candidates(d, start, mb, seed, cache)

    gen = fresh(max(best[0] + 1, mb // 4))
    while True:
        rem = deadline - time.monotonic()
        if rem < 2.5:
            break
        try:
            T, K, m, k, r = next(gen)
        except StopIteration:
            break
        if T <= best[0] or (K, m, k, r) in tried:
            continue
        tried.add((K, m, k, r))
        slice_s = min(max(2.0, 0.15 * rem), rem - 1.0)
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(slice_s, 2), K, m, k, r],
                             stdin_graph=None, timeout=slice_s + 10.0)
            n, edges = lib.parse_graph_text(text)
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
            gen = fresh(max(best[0] + 1, int(best[0] * 1.02)))
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        deadline = t0 + min(0.8 * time_limit, time_limit - 8.0)
        try:
            best = _climb(d, D, seed, deadline, best, mb)
        except Exception:
            pass  # keep the valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
