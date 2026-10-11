"""Haar-graph search program.

Main idea: the parent engine grows or lifts random semidirect-product voltage graphs. This version
instead searches the cyclic Haar graphs H(M, S) exhaustively. H(M, S) has parts A = Z_M and B = Z_M,
with a_i ~ b_{i+s} for s in S, |S| = d, and 0 in S (WLOG, by translating S). Every such graph is
d-regular and bipartite on 2M vertices. Translations are transitive on each part, so the diameter
check needs only two BFS runs, from a_0 and b_0. The C engine scans M upward and keeps the largest
M that passes. Sets S are enumerated exhaustively when feasible and sampled otherwise.

Fallback: Python keeps the best valid algebraic start (K_{d,d}, PG(2,d-1), W(q), Araujo-Pardo-Lopez),
and only replaces it with a C result that passes lib.is_valid and is strictly larger.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 2000
#define MAXK 40
#define SAMPLE_LIMIT 300000.0

static int d, D, K;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int M;
static int S[MAXK];
static int best_M = 0;
static int best_S[MAXK];

static unsigned stamp_arr[2 * MAXM];
static int dist_arr[2 * MAXM];
static int queue_arr[2 * MAXM];
static unsigned cur_stamp = 0;

/* Number of vertices within distance D of src in H(M, S). */
static int reach_count(int src) {
    cur_stamp++;
    int head = 0, tail = 0;
    queue_arr[tail++] = src;
    stamp_arr[src] = cur_stamp;
    dist_arr[src] = 0;
    while (head < tail) {
        int v = queue_arr[head++];
        int dv = dist_arr[v];
        if (dv >= D) continue;
        for (int t = 0; t < K; t++) {
            int u;
            if (v < M) u = M + (v + S[t]) % M;
            else u = (v - M - S[t] + M) % M;
            if (stamp_arr[u] != cur_stamp) {
                stamp_arr[u] = cur_stamp;
                dist_arr[u] = dv + 1;
                queue_arr[tail++] = u;
            }
        }
    }
    return tail;
}

/* Diameter test: BFS from a_0 covers all pairs (a_i, *) by translation,
 * BFS from b_0 covers all pairs (b_i, *). */
static int haar_ok(void) {
    int n2 = 2 * M;
    if (reach_count(0) != n2) return 0;
    if (reach_count(M) != n2) return 0;
    return 1;
}

static int try_combo(const int *c, int k) {
    S[0] = 0;
    for (int i = 0; i < k; i++) S[i + 1] = c[i];
    return haar_ok();
}

static void record_best(void) {
    best_M = M;
    memcpy(best_S, S, sizeof(int) * (size_t)K);
}

static int search_M(int m, int k) {
    if (m - 1 < k) return 0;
    double total = 1.0;
    for (int i = 0; i < k; i++) total = total * (double)(m - 1 - i) / (double)(i + 1);
    M = m;
    int c[MAXK];
    long cnt = 0;
    if (total <= SAMPLE_LIMIT) {
        for (int i = 0; i < k; i++) c[i] = i + 1;
        for (;;) {
            if (try_combo(c, k)) { record_best(); return 1; }
            if ((++cnt & 1023) == 0 && now() > t_end) return 0;
            int i = k - 1;
            while (i >= 0 && c[i] == m - k + i) i--;
            if (i < 0) return 0;
            c[i]++;
            for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
        }
    }
    for (long it = 0; it < (long)SAMPLE_LIMIT; it++) {
        if ((it & 1023) == 0 && now() > t_end) return 0;
        for (int i = 0; i < k; i++) {
            int v, dup;
            do {
                v = 1 + rndint(m - 1);
                dup = 0;
                for (int j = 0; j < i; j++)
                    if (c[j] == v) { dup = 1; break; }
            } while (dup);
            c[i] = v;
        }
        for (int i = 1; i < k; i++) {
            int x = c[i], j = i - 1;
            while (j >= 0 && c[j] > x) { c[j + 1] = c[j]; j--; }
            c[j + 1] = x;
        }
        if (try_combo(c, k)) { record_best(); return 1; }
    }
    return 0;
}

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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    K = d;
    if (d < 2 || D < 2 || d > MAXK) {
        printf("0 0\n");
        return 0;
    }

    long n0 = 0, m0 = 0;
    if (scanf("%ld %ld", &n0, &m0) == 2) {
        for (long e = 0; e < m0; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) break;
        }
    } else {
        n0 = 0;
    }

    /* Haar order 2M must not exceed the Moore bound 2 * sum_{i<D} (d-1)^i. */
    long msum = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        msum += pw;
        pw *= (d - 1);
        if (msum > 1000000) break;
    }
    long Mmax = msum < MAXM - 1 ? msum : MAXM - 1;
    long Mstart = n0 / 2 + 1;
    if (Mstart < d) Mstart = d;

    for (long m = Mstart; m <= Mmax && now() < t_end; m++) {
        search_M((int)m, d - 1);
    }

    if (best_M > 0) {
        int m = best_M;
        printf("%d %d\n", 2 * m, m * d);
        for (int i = 0; i < m; i++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i, m + (i + best_S[t]) % m);
    } else {
        printf("0 0\n");
    }
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
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
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
