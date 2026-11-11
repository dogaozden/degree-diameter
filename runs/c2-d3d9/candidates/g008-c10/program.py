"""Block-lift annealing: multi-vertex bi-Cayley lifts searched by simulated annealing.

New idea: a base bipartite multigraph with k A-blocks and k B-blocks, made d-regular by
d perfect matchings between the blocks (permutations sig[j]). Each dart j from A-block i
gets a voltage g in a metacyclic group G of order N, so A_{i,x} ~ B_{sig_j(i), x*g}.
The lift has 2kN vertices. Left multiplication by G is an automorphism, so the diameter
test needs only 2k BFS runs (one per block representative), each truncated at depth D.

Search: for each (k, N) candidate with order 2kN >= lo, anneal the voltages and the
permutations to minimize (number of vertex pairs at distance > D from block representatives)
plus a penalty for parallel edges. Candidates are tried in increasing order, so the first
successes are the smallest graphs that beat the current best. k = 1 is the parent's
bi-Cayley case, so it is covered as well. The C program verifies the final graph with a
full BFS before printing, and Python checks it again with lib.is_valid.
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

#define MAXG 1024
#define MAXK 6
#define MAXV (2 * MAXK * MAXG)
#define MAXDEG 16
#define MAXGRP 4096
#define MAXCAND 8192
#define ITERS 20000
#define DUPW 40

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
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Nonabelian groups (r != 1) first, then abelian ones. */
static void enum_groups(int n) {
    ngroups = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= n; m++) {
            if (n % m) continue;
            int k = n / m;
            if (m == 1) {
                if (pass == 1 && ngroups < MAXGRP) {
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
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (ngroups < MAXGRP) {
                    groups[ngroups].m = m;
                    groups[ngroups].k = k;
                    groups[ngroups].r = r;
                    ngroups++;
                }
            }
        }
    }
}

/* Current group: element (a,b) coded a*k+b, identity 0. */
static int NG;
static int MT[MAXG * MAXG];
static int INV[MAXG];

static void build_group(Grp G) {
    int n = G.m * G.k;
    NG = n;
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

/* ---------------------------------------------------------- block lift state */

static int KB;                       /* blocks per side */
static int sig[MAXDEG][MAXK];        /* dart j from A-block i goes to B-block sig[j][i] */
static int sinv[MAXDEG][MAXK];       /* sinv[j][t] = i with sig[j][i] = t */
static int gv[MAXDEG][MAXK];         /* voltage of dart j at A-block i */

typedef struct {
    int sig[MAXDEG][MAXK], sinv[MAXDEG][MAXK], gv[MAXDEG][MAXK];
} State;

static void save_state(State *s) {
    memcpy(s->sig, sig, sizeof sig);
    memcpy(s->sinv, sinv, sizeof sinv);
    memcpy(s->gv, gv, sizeof gv);
}
static void load_state(const State *s) {
    memcpy(sig, s->sig, sizeof sig);
    memcpy(sinv, s->sinv, sizeof sinv);
    memcpy(gv, s->gv, sizeof gv);
}

/* Vertex ids: A-block i, element x -> i*NG + x; B-block t, element y -> KB*NG + t*NG + y. */
static inline int nbr(int v, int j) {
    int half = KB * NG;
    if (v < half) {
        int i = v / NG, x = v - i * NG;
        int t = sig[j][i];
        int y = MT[x * NG + gv[j][i]];
        return half + t * NG + y;
    } else {
        int w = v - half;
        int t = w / NG, y = w - t * NG;
        int i = sinv[j][t];
        int x = MT[y * NG + INV[gv[j][i]]];
        return i * NG + x;
    }
}

static void random_state(void) {
    for (int j = 0; j < d; j++) {
        int p[MAXK];
        for (int i = 0; i < KB; i++) p[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
        }
        for (int i = 0; i < KB; i++) {
            sig[j][i] = p[i];
            sinv[j][p[i]] = i;
        }
        for (int i = 0; i < KB; i++) gv[j][i] = rndint(NG);
    }
}

static void mutate(void) {
    if (KB > 1 && rnd01() < 0.15) {
        int j = rndint(d);
        int a = rndint(KB), b = rndint(KB);
        if (a == b) return;
        int tmp = sig[j][a]; sig[j][a] = sig[j][b]; sig[j][b] = tmp;
        for (int i = 0; i < KB; i++) sinv[j][sig[j][i]] = i;
    } else {
        int j = rndint(d), i = rndint(KB);
        gv[j][i] = rndint(NG);
    }
}

/* ---------------------------------------------------------- cost */

static int distv[MAXV], qv[MAXV];

/* Number of vertices NOT within distance D of src. */
static int bfs_bad(int src) {
    int V = 2 * KB * NG;
    for (int i = 0; i < V; i++) distv[i] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int v = qv[head++];
        int dv = distv[v];
        if (dv >= D) continue;
        for (int j = 0; j < d; j++) {
            int u = nbr(v, j);
            if (distv[u] < 0) { distv[u] = dv + 1; qv[tail++] = u; }
        }
    }
    return V - tail;
}

/* Parallel edges: two darts from the same A-block to the same B-block with equal voltage. */
static long dup_count(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int j = 0; j < d; j++)
            for (int j2 = j + 1; j2 < d; j2++)
                if (sig[j][i] == sig[j2][i] && gv[j][i] == gv[j2][i]) c++;
    return c;
}

static long eval_cost(void) {
    long c = 0;
    int half = KB * NG;
    for (int s = 0; s < 2 * KB; s++) {
        int src = (s < KB) ? s * NG : half + (s - KB) * NG;
        c += bfs_bad(src);
    }
    c += DUPW * dup_count();
    return c;
}

/* ---------------------------------------------------------- annealing */

static int anneal_run(double until) {
    long cur = eval_cost();
    if (cur == 0) return 1;
    double T0 = 2.0, T1 = 0.05;
    State saved;
    for (long it = 0; it < ITERS; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)it / ITERS);
        save_state(&saved);
        mutate();
        long c = eval_cost();
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
            cur = c;
        } else {
            load_state(&saved);
        }
        if (cur == 0) return 1;
    }
    return 0;
}

static int bestKB = 0;
static Grp bestG;
static State best_st;

static int search_candidate(int kb, int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    KB = kb;
    while (now() < until) {
        Grp G = groups[rndint(ngroups)];
        build_group(G);
        random_state();
        if (anneal_run(until)) {
            bestKB = kb;
            bestG = G;
            save_state(&best_st);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- candidates */

typedef struct { int kb, n; long ord; } Cand;
static Cand cands[MAXCAND];
static int ncand;

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->ord != y->ord) return x->ord < y->ord ? -1 : 1;
    return x->kb - y->kb;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void build_explicit(void) {
    int half = KB * NG, V = 2 * half;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int v = 0; v < half; v++)
        for (int j = 0; j < d; j++) {
            int u = nbr(v, j);
            adjl[v][degl[v]++] = u;
            adjl[u][degl[u]++] = v;
        }
}

static int verify_explicit(int V) {
    static int dd[MAXV], qq[MAXV];
    for (int v = 0; v < V; v++) {
        if (degl[v] != d) return 0;
        for (int a = 0; a < degl[v]; a++)
            for (int b = a + 1; b < degl[v]; b++)
                if (adjl[v][a] == adjl[v][b]) return 0;
    }
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd[i] = -1;
        int head = 0, tail = 0;
        dd[s] = 0;
        qq[tail++] = s;
        while (head < tail) {
            int v = qq[head++];
            if (dd[v] >= D) continue;
            for (int i = 0; i < degl[v]; i++) {
                int u = adjl[v][i];
                if (dd[u] < 0) { dd[u] = dd[v] + 1; qq[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void print_explicit(int V) {
    int half = V / 2;
    printf("%d %d\n", V, half * d);
    for (int v = 0; v < half; v++)
        for (int i = 0; i < degl[v]; i++)
            printf("%d %d\n", v, adjl[v][i]);
}

static void set_complete(void) {
    int V = 2 * d;
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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

    if (d < 2 || d > MAXDEG || D < 2) { set_complete(); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long moore = moore_bound();
    ncand = 0;
    for (int kb = 1; kb <= MAXK; kb++) {
        for (int n = 2; n < MAXG; n++) {
            long ord = 2L * kb * n;
            if (ord > moore) break;
            if (ord < lo) continue;
            if (ncand < MAXCAND) {
                cands[ncand].kb = kb;
                cands[ncand].n = n;
                cands[ncand].ord = ord;
                ncand++;
            }
        }
    }
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    double slice = budget / 60.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 2.0) slice = 2.0;

    long bestOrd = 0;
    int have = 0;
    for (int ci = 0; ci < ncand; ci++) {
        Cand c = cands[ci];
        if (c.ord <= bestOrd) continue;
        double nw = now();
        if (nw >= t_end) break;
        double until = nw + slice;
        if (until > t_end) until = t_end;
        if (search_candidate(c.kb, c.n, until)) {
            have = 1;
            bestOrd = c.ord;
        }
    }

    int ok = 0;
    if (have) {
        KB = bestKB;
        build_group(bestG);
        load_state(&best_st);
        build_explicit();
        int V = 2 * KB * NG;
        ok = verify_explicit(V);
        if (ok) print_explicit(V);
    }
    if (!ok) set_complete();
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

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    # Only orders from about 0.45 of the Moore bound upward are worth searching.
    lo = max(best[0] + 1, int(0.45 * moore))
    if lo > 12000:
        lo = best[0] + 1
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
