"""Cayley-bipartite search for the d=16, D=3 record.

Previous approach: twin blow-up of PG(2,q), which is capped at the 394 record.
New approach: a bipartite Cayley graph on a group G of order N. Vertices are
A-copies and B-copies of G, and a_g ~ b_{g s} for s in S, with |S| = d.
Left translation is an automorphism, so validity only needs eccentricities
from a_e and b_e. Each evaluation is therefore two BFS passes over 2N vertices,
which is cheap. Simulated annealing over S searches for groups of order
N = 198, 199, ... (giving 2N > 394 vertices). Groups are semidirect products
Z_m x| Z_k. A full all-pairs check runs in C before any solution is printed.
Fallback: the best structured start (or K_{d,d}), so every case stays valid.
Untested in this environment; any failure falls back to the structured start.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite Cayley-graph search.
 *
 * Usage:   prog d D seed time_limit minN
 * Output:  "n m" then edges (valid graph, possibly "0 0" if nothing found).
 *
 * Graph: group G = Z_m x|_r Z_k of order N, connection set S (|S| = d distinct).
 * A-vertex g (id g), B-vertex h (id N+h); edge g -- N + g*s for s in S.
 * Degree is d on both sides. Left translation is an automorphism, so the diameter
 * is <= D iff every vertex is within D of a_e and of b_e. Simulated annealing
 * minimises the number of vertices missed by those two balls.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXDEG 40

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

static int gcd_i(int a, int b) {
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

/* ------------------------------------------------------------------ groups */

static int GN, GM, GK, GR;
static int rp[MAXG];
static int MUL[MAXG][MAXG];
static int INV[MAXG];

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; GN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++) {
            int a = x / k, b = x % k, c = y / k, e = y % k;
            MUL[x][y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
}

/* Random semidirect group of order N with r^k = 1 mod m. 30% of draws are cyclic. */
static int random_group(int N) {
    for (int tries = 0; tries < 200000; tries++) {
        int m, k, r;
        if (rndint(10) < 3) {
            m = N; k = 1; r = 1;
        } else {
            m = 1 + rndint(N);
            if (N % m) continue;
            k = N / m;
            r = m > 1 ? 1 + rndint(m - 1) : 1;
        }
        if (gcd_i(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        set_group(m, k, r);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ search */

static int S[MAXDEG];
static unsigned char INS[MAXG];

/* Number of vertices (both sides) NOT within D steps of the source vertex. */
static int reach_missing(int side, int src) {
    static unsigned char vis[2 * MAXG];
    static int cur[2 * MAXG], nxt[2 * MAXG];
    int n2 = 2 * GN;
    memset(vis, 0, (size_t)n2);
    int nc = 0, total = 1;
    int start = side == 0 ? src : GN + src;
    vis[start] = 1;
    cur[nc++] = start;
    for (int lev = 0; lev < D && nc > 0; lev++) {
        int nn = 0;
        for (int i = 0; i < nc; i++) {
            int v = cur[i];
            if (v < GN) {
                for (int j = 0; j < d; j++) {
                    int w = GN + MUL[v][S[j]];
                    if (!vis[w]) { vis[w] = 1; nxt[nn++] = w; }
                }
            } else {
                int h = v - GN;
                for (int j = 0; j < d; j++) {
                    int w = MUL[h][INV[S[j]]];
                    if (!vis[w]) { vis[w] = 1; nxt[nn++] = w; }
                }
            }
        }
        memcpy(cur, nxt, sizeof(int) * (size_t)nn);
        nc = nn;
        total += nn;
    }
    return n2 - total;
}

static int cost(void) { return reach_missing(0, 0) + reach_missing(1, 0); }

/* Simulated annealing on S for the current group. Returns 1 if cost 0 is reached. */
static int sa_trial(long max_steps, double until) {
    memset(INS, 0, (size_t)GN);
    for (int j = 0; j < d; j++) {
        int x;
        do x = rndint(GN); while (INS[x]);
        INS[x] = 1;
        S[j] = x;
    }
    int c = cost();
    double T = 1.0;
    for (long step = 0; step < max_steps; step++) {
        if (c == 0) return 1;
        if ((step & 255) == 0 && now() > until) return 0;
        int i = rndint(d);
        int old = S[i], nw;
        do nw = rndint(GN); while (INS[nw]);
        S[i] = nw;
        INS[old] = 0;
        INS[nw] = 1;
        int nc = cost();
        if (nc <= c || rnd01() < exp((double)(c - nc) / T)) {
            c = nc;
        } else {
            S[i] = old;
            INS[nw] = 0;
            INS[old] = 1;
        }
        T *= 0.9995;
        if (T < 0.15) T = 1.0;
    }
    return c == 0;
}

/* Independent all-pairs check on the full graph (2N vertices). */
static int verify_full(void) {
    int n = 2 * GN;
    static int dist[2 * MAXG], q[2 * MAXG];
    for (int src = 0; src < n; src++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        q[t++] = src;
        dist[src] = 0;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            if (v < GN) {
                for (int j = 0; j < d; j++) {
                    int w = GN + MUL[v][S[j]];
                    if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
                }
            } else {
                int hh = v - GN;
                for (int j = 0; j < d; j++) {
                    int w = MUL[hh][INV[S[j]]];
                    if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
                }
            }
        }
        for (int v = 0; v < n; v++)
            if (dist[v] < 0) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [minN]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : d + 1;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    int maxN = (int)(moore / 2);
    if (maxN > MAXG) maxN = MAXG;
    if (minN < d + 1) minN = d + 1;

    int bestN = 0, bestm = 0, bestk = 0, bestr = 0;
    static int bestS[MAXDEG];

    for (int N = minN; N <= maxN; N++) {
        double until = now() + (t_end - now()) * 0.7;
        int found = 0;
        while (!found && now() < until) {
            if (!random_group(N)) break;
            if (sa_trial(40000, until) && verify_full()) {
                found = 1;
                bestN = N;
                bestm = GM; bestk = GK; bestr = GR;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
            }
        }
        if (!found) break;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestm, bestk, bestr);
    memcpy(S, bestS, sizeof(int) * (size_t)d);
    printf("%d %ld\n", 2 * bestN, (long)bestN * d);
    for (int g = 0; g < bestN; g++)
        for (int j = 0; j < d; j++)
            printf("%d %d\n", g, bestN + MUL[g][S[j]]);
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


def conic_blowup(d, D):
    """Twin-blow-up of PG(2,q) with q = d-3 odd, using a conic and a dual conic.

    Gives 2(q^2+q+1) + 2(q+1) vertices, which is 394 for q = 13 (d = 16).
    """
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)   # points 0..m-1, lines m..2m-1
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def starts(d, D):
    """Candidate structured start graphs (validity is checked later)."""
    out = []
    try:
        ks = known_start(d, D)
        if ks is not None:
            out.append(ks)
    except Exception:
        pass
    try:
        cb = conic_blowup(d, D)
        if cb is not None:
            out.append(cb)
    except Exception:
        pass
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = None
    for cand in starts(d, D):
        try:
            ok = lib.is_valid(cand[0], cand[1], d, D)
        except Exception:
            ok = False
        if ok and (start is None or cand[0] > start[0]):
            start = cand
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}: always valid

    if d < 2 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    # New engine: Cayley-bipartite search for orders above the current best.
    minN = best[0] // 2 + 1
    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 0.5:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget, minN], stdin_graph=None,
                             timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass   # keep the valid structured fallback
    return best
