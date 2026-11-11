"""Lifted bi-Cayley search: voltage lifts over metacyclic groups with a base of b vertices per side.

Vertices are A_{i,x} and B_{j,y} for base index i, j in 0..b-1 and group elements x, y. Each
base dart k gives edges A_{i,x} ~ B_{pi_k(i), x*g_{k,i}}. Left multiplication is an automorphism,
so the diameter only needs BFS from A_{i,1} and B_{j,1} for each base index (2b sources). Order
is 2*b*|G|. b = 1 is the earlier bi-Cayley family (a Haar-type lift with d distinct voltages).

For each total order T (ascending, starting above the current best), and each base size b that
divides T/2, the C engine runs simulated-annealing-like hill climbing on the voltages of a random
metacyclic group. The cost is the number of (source, vertex) pairs at distance > D. A zero-cost
configuration is verified again (all sources, no duplicate neighbours) before it is printed.
If nothing beats the start, the C program prints nothing useful and Python keeps the valid start.
"""
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV 2048
#define MAXDEG 16
#define MAXB 6
#define MAXGRP 4096
#define STALL 4000

static int d, D;
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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXGRP) {
                groups[ngroups].m = 1;
                groups[ngroups].k = k;
                groups[ngroups].r = 0;
                ngroups++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGRP) {
                groups[ngroups].m = m;
                groups[ngroups].k = k;
                groups[ngroups].r = r;
                ngroups++;
            }
        }
    }
}

static int MT[MAXG * MAXG]; /* multiplication table of the current group */
static int INV[MAXG];
static int NN;

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    static int rp[MAXG];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.k, b = x % G.k;
        for (int y = 0; y < n; y++) {
            int c = y / G.k, e = y % G.k;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.k + (b + e) % G.k;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- lift state */

static int B_;   /* base size b: b vertices per side */
static int N_;   /* group order */
static int pi_[MAXDEG][MAXB];   /* dart k from A_i goes to B_{pi_[k][i]} */
static int gv_[MAXDEG][MAXB];   /* voltage of dart k from A_i */
static int inc_i[MAXB][MAXDEG], inc_k[MAXB][MAXDEG]; /* darts entering B_j */

static void build_inc(int b) {
    for (int j = 0; j < b; j++) {
        int cnt = 0;
        for (int k = 0; k < d; k++)
            for (int i = 0; i < b; i++)
                if (pi_[k][i] == j) {
                    inc_i[j][cnt] = i;
                    inc_k[j][cnt] = k;
                    cnt++;
                }
    }
}

/* Neighbour t of vertex v in the lift. A_{i,x} = i*n + x; B_{j,y} = b*n + j*n + y. */
static int nbr_of(int v, int t) {
    int n = N_, b = B_;
    if (v < b * n) {
        int i = v / n, x = v % n;
        int j = pi_[t][i];
        int y = MT[x * n + gv_[t][i]];
        return b * n + j * n + y;
    } else {
        int w = v - b * n;
        int j = w / n, y = w % n;
        int i = inc_i[j][t], k = inc_k[j][t];
        int x = MT[y * n + INV[gv_[k][i]]];
        return i * n + x;
    }
}

static int dup_free_all(int b) {
    for (int i = 0; i < b; i++)
        for (int k = 0; k < d; k++)
            for (int k2 = k + 1; k2 < d; k2++)
                if (pi_[k][i] == pi_[k2][i] && gv_[k][i] == gv_[k2][i]) return 0;
    return 1;
}

static int dup_free_for(int k, int i, int val) {
    for (int k2 = 0; k2 < d; k2++) {
        if (k2 == k) continue;
        if (pi_[k2][i] == pi_[k][i] && gv_[k2][i] == val) return 0;
    }
    return 1;
}

/* Base multigraph connected? Label propagation on the 2b base vertices. */
static int base_connected(int b) {
    int lab[2 * MAXB];
    for (int v = 0; v < 2 * b; v++) lab[v] = v;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int k = 0; k < d; k++)
            for (int i = 0; i < b; i++) {
                int a = i, c = b + pi_[k][i];
                int m = lab[a] < lab[c] ? lab[a] : lab[c];
                if (lab[a] != m) { lab[a] = m; changed = 1; }
                if (lab[c] != m) { lab[c] = m; changed = 1; }
            }
    }
    for (int v = 0; v < 2 * b; v++)
        if (lab[v] != 0) return 0;
    return 1;
}

static int init_lift(int b, int n) {
    for (int attempt = 0; attempt < 500; attempt++) {
        for (int k = 0; k < d; k++) {
            int p[MAXB];
            for (int i = 0; i < b; i++) p[i] = i;
            if (k > 0)
                for (int i = b - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = p[i]; p[i] = p[j]; p[j] = t;
                }
            for (int i = 0; i < b; i++) pi_[k][i] = p[i];
        }
        for (int k = 0; k < d; k++)
            for (int i = 0; i < b; i++)
                gv_[k][i] = rndint(n);
        if (!dup_free_all(b)) continue;
        build_inc(b);
        if (!base_connected(b)) continue;
        return 1;
    }
    return 0;
}

/* ---------------------------------------------------------- cost */

static int distb[MAXV], qb[MAXV];

/* Number of vertices within distance D of src. */
static int reach_count(int src, int V) {
    for (int i = 0; i < V; i++) distb[i] = -1;
    int head = 0, tail = 0;
    distb[src] = 0;
    qb[tail++] = src;
    while (head < tail) {
        int v = qb[head++];
        int dv = distb[v];
        if (dv >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = nbr_of(v, t);
            if (distb[u] < 0) {
                distb[u] = dv + 1;
                qb[tail++] = u;
            }
        }
    }
    return tail;
}

/* Sum over the 2b sources (A_{i,e}, B_{j,e}) of the number of vertices at distance > D. */
static int cost_all(void) {
    int b = B_, n = N_, V = 2 * b * n;
    int total = 0;
    for (int i = 0; i < b; i++) total += V - reach_count(i * n, V);
    for (int j = 0; j < b; j++) total += V - reach_count(b * n + j * n, V);
    return total;
}

/* ---------------------------------------------------------- search */

static int bestT = 0, bestB = 0, bestN = 0;
static Grp bestG;
static int bestPi[MAXDEG][MAXB], bestGv[MAXDEG][MAXB];

/* Hill-climb voltages for base size b and group order n. Returns 1 on success (stored in best*). */
static int search_candidate(int b, int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    B_ = b;
    N_ = n;
    int off = rndint(ngroups);
    for (int it = 0; now() < until; it++) {
        Grp G = groups[(off + it) % ngroups];
        build_group(G);
        if (!init_lift(b, n)) continue;
        int cur = cost_all();
        int rbest = cur, stall = 0;
        while (cur > 0 && stall <= STALL && now() < until) {
            int k = rndint(d), i = rndint(b);
            int val = rndint(n);
            int old = gv_[k][i];
            if (val == old) continue;
            if (!dup_free_for(k, i, val)) { stall++; continue; }
            gv_[k][i] = val;
            int c = cost_all();
            if (c <= cur || rndint(1000) < 3) {
                cur = c;
                if (cur < rbest) { rbest = cur; stall = 0; }
                else stall++;
            } else {
                gv_[k][i] = old;
                stall++;
            }
        }
        if (cur == 0) {
            bestT = 2 * b * n;
            bestB = b;
            bestN = n;
            bestG = G;
            memcpy(bestPi, pi_, sizeof pi_);
            memcpy(bestGv, gv_, sizeof gv_);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget lo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    long lo = atol(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget;

    long moore = moore_bound();
    long Tmax = moore;
    if (Tmax > MAXV) Tmax = MAXV;

    long T = lo;
    if (T < 2L * (d + 1)) T = 2L * (d + 1);
    if (T & 1) T++;

    double slice = budget / 80.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 1.5) slice = 1.5;

    for (; T <= Tmax && now() < t_end; T += 2) {
        for (int b = 1; b <= MAXB && now() < t_end; b++) {
            if (T % (2L * b)) continue;
            long n = T / (2L * b);
            if (n < d || n > MAXG) continue;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (search_candidate(b, (int)n, until)) break;
        }
    }

    if (bestT == 0) { printf("0 0\n"); return 0; }

    B_ = bestB;
    N_ = bestN;
    build_group(bestG);
    memcpy(pi_, bestPi, sizeof pi_);
    memcpy(gv_, bestGv, sizeof gv_);
    build_inc(B_);

    int half = B_ * N_;
    int V = 2 * half;
    int ok = 1;
    for (int s = 0; s < V && ok; s++)
        if (reach_count(s, V) != V) ok = 0;
    for (int v = 0; v < half && ok; v++)
        for (int t = 0; t < d && ok; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (nbr_of(v, t) == nbr_of(v, t2)) { ok = 0; break; }
    if (!ok) { printf("0 0\n"); return 0; }

    printf("%d %d\n", V, half * d);
    for (int v = 0; v < half; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, nbr_of(v, t));
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    # Only search for totals above the current best, and never below 0.45 of the Moore bound.
    lo = max(best[0] + 2, int(0.45 * moore))
    if lo > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
