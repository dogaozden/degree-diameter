"""Bi-Cayley seed plus cubic gadget growth with bitset annealing.

Stage 1 (C): scan bi-Cayley graphs over metacyclic groups Z_m x| Z_k, with
A_x ~ B_{x s} for s in S = {0, s_1, ..., s_{d-1}}, and keep the largest order
that has diameter <= D. This is the parent's search, with a smaller time share.

Stage 2 (C, new): start from that cubic bipartite graph and grow it by one
"gadget" at a time. The gadget removes two edges (a,b), (a2,b2) and adds a new
A-vertex x and a new B-vertex y with edges x-b, x-b2, a-y, a2-y, x-y. Degrees
stay at most 3 and the graph stays bipartite. Each grown graph is then repaired
by simulated annealing over 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep
every degree and the bipartition. The cost is the number of vertex pairs at
distance > D. Distances come from bitset BFS, run as D rounds of OR over
neighbour bitsets. The last graph with zero bad pairs is printed.

Python keeps the best of the known start and the C result, and checks
everything with lib.is_valid.
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
#define MAXN 560
#define MAXV (2 * MAXN + 4)
#define WMAX ((MAXV + 63) / 64)
#define MAXDEG 16
#define MAXGRP 4096
#define MAXE (MAXDEG * MAXN + 16)
#define TEMP 0.7

static int d, D;
static double t_end2;

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

static int popcount64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

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

static int MT[MAXG * MAXG];
static int INV[MAXG];
static int NN;

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

/* ---------------------------------------------------------- bi-Cayley check */

static int dist_[MAXV], queue_[MAXV];

static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

static int bestN = 0;
static Grp bestG;
static int bestS[MAXDEG];

static int search_n(int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    int S[MAXDEG];
    while (now() < until) {
        for (int gi = 0; gi < ngroups; gi++) {
            if (now() >= until) break;
            build_group(groups[gi]);
            for (int t = 0; t < 200; t++) {
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    bestN = n;
                    bestG = groups[gi];
                    memcpy(bestS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit bipartite graph
 * A vertices are 0..nA-1, B vertices are nA..2nA-1 (the gadget relabels as needed). */

static int nA, ne;
static int eu[MAXE], ev[MAXE];
static int adj[MAXV][MAXDEG], dg[MAXV];

static int sv_nA = 0, sv_ne = 0;
static int sv_eu[MAXE], sv_ev[MAXE];

static void rebuild_adj(void) {
    int V = 2 * nA;
    for (int v = 0; v < V; v++) dg[v] = 0;
    for (int i = 0; i < ne; i++) {
        int a = eu[i], b = ev[i];
        adj[a][dg[a]++] = b;
        adj[b][dg[b]++] = a;
    }
}

static int is_adj(int v, int u) {
    for (int k = 0; k < dg[v]; k++)
        if (adj[v][k] == u) return 1;
    return 0;
}

static void nb_replace(int v, int old, int nw) {
    for (int k = 0; k < dg[v]; k++)
        if (adj[v][k] == old) { adj[v][k] = nw; return; }
}

static void load_bicayley(void) {
    int n = bestN;
    build_group(bestG);
    nA = n;
    ne = 0;
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++) {
            eu[ne] = x;
            ev[ne] = n + MT[x * n + bestS[i]];
            ne++;
        }
    rebuild_adj();
}

static void save_best(void) {
    sv_nA = nA;
    sv_ne = ne;
    memcpy(sv_eu, eu, sizeof(int) * (size_t)ne);
    memcpy(sv_ev, ev, sizeof(int) * (size_t)ne);
}

static void restore_best(void) {
    nA = sv_nA;
    ne = sv_ne;
    memcpy(eu, sv_eu, sizeof(int) * (size_t)ne);
    memcpy(ev, sv_ev, sizeof(int) * (size_t)ne);
    rebuild_adj();
}

/* Bitset all-pairs ball of radius D; returns the number of unordered pairs at distance > D. */
static uint64_t BUF0[MAXV * WMAX], BUF1[MAXV * WMAX];

static long bad_count(void) {
    int V = 2 * nA;
    int W = (V + 63) / 64;
    uint64_t *cur = BUF0, *nxt = BUF1;
    memset(cur, 0, sizeof(uint64_t) * (size_t)V * WMAX);
    for (int v = 0; v < V; v++) cur[v * WMAX + v / 64] |= 1ULL << (v % 64);
    for (int step = 0; step < D; step++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            for (int w = 0; w < W; w++) {
                uint64_t x = cur[v * WMAX + w];
                for (int k = 0; k < dg[v]; k++) x |= cur[adj[v][k] * WMAX + w];
                nxt[v * WMAX + w] = x;
                if (x != cur[v * WMAX + w]) changed = 1;
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long tot = 0;
    for (int v = 0; v < V; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popcount64(cur[v * WMAX + w]);
        tot += V - c;
    }
    return tot / 2;
}

/* 2-switch: edges i=(a,b), j=(c,e) become (a,e), (c,b). Keeps degrees and bipartiteness.
 * Applying it again to the same (i, j) undoes it. Returns 0 if it would create a multi-edge. */
static int try_switch(int i, int j) {
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (a == c || b == e) return 0;
    if (is_adj(a, e) || is_adj(c, b)) return 0;
    nb_replace(a, b, e);
    nb_replace(b, a, c);
    nb_replace(c, e, b);
    nb_replace(e, c, a);
    ev[i] = e;
    ev[j] = b;
    return 1;
}

/* Cubic gadget: remove (a,b), (a2,b2); add new A-vertex x = n and new B-vertex y = 2n+1
 * with edges x-b, x-b2, a-y, a2-y, x-y. Old B ids shift by one. Every degree stays 3. */
static void gadget(void) {
    int n = nA;
    if (n + 2 >= MAXN || ne + 5 > MAXE) return;
    int i, j;
    do {
        i = rndint(ne);
        j = rndint(ne);
    } while (i == j || eu[i] == eu[j] || ev[i] == ev[j]);
    int a = eu[i], b = ev[i], a2 = eu[j], b2 = ev[j];
    static int nu[MAXE], nw[MAXE];
    int m = 0;
    for (int k = 0; k < ne; k++) {
        if (k == i || k == j) continue;
        int u = eu[k], w = ev[k];
        if (w >= n) w++;
        nu[m] = u; nw[m] = w; m++;
    }
    int x = n, y = 2 * n + 1;
    nu[m] = x; nw[m] = b + 1; m++;
    nu[m] = x; nw[m] = b2 + 1; m++;
    nu[m] = a; nw[m] = y; m++;
    nu[m] = a2; nw[m] = y; m++;
    nu[m] = x; nw[m] = y; m++;
    memcpy(eu, nu, sizeof(int) * (size_t)m);
    memcpy(ev, nw, sizeof(int) * (size_t)m);
    ne = m;
    nA = n + 1;
    rebuild_adj();
}

/* Simulated annealing over 2-switches. Returns the remaining number of bad pairs (0 = success). */
static long anneal(double until) {
    long cur = bad_count();
    long it = 0;
    while (cur > 0) {
        if ((it & 255) == 0 && now() >= until) break;
        it++;
        int i = rndint(ne), j = rndint(ne);
        if (i == j) continue;
        if (!try_switch(i, j)) continue;
        long nw = bad_count();
        long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / TEMP)) {
            cur = nw;
        } else {
            try_switch(i, j); /* revert */
        }
    }
    return cur;
}

static void stage2(void) {
    while (now() < t_end2) {
        restore_best();
        gadget();
        double rem = t_end2 - now();
        double chunk = rem * 0.35;
        if (chunk < 1.0) chunk = rem;
        long r = anneal(now() + chunk);
        if (r == 0) save_best();
    }
}

static void print_saved(void) {
    int V = 2 * sv_nA;
    printf("%d %d\n", V, sv_ne);
    for (int i = 0; i < sv_ne; i++) printf("%d %d\n", sv_eu[i], sv_ev[i]);
}

static void set_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int nlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }

    double t0 = now();
    double stage1_end = t0 + budget * 0.5;
    t_end2 = t0 + budget * 0.9;

    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXN - 2) nmax = MAXN - 2;
    int nstart = nlo;
    if (nstart < d + 1) nstart = d + 1;
    double slice = (budget * 0.5) / 30.0;
    if (slice < 0.4) slice = 0.4;
    if (slice > 3.0) slice = 3.0;

    if (d >= 2 && D >= 2) {
        for (int n = nstart; n <= nmax && now() < stage1_end; n++) {
            double until = now() + slice;
            if (until > stage1_end) until = stage1_end;
            search_n(n, until);
        }
    }

    int ok = 0;
    if (bestN > 0) {
        load_bicayley();
        if (bad_count() == 0) {
            save_best();
            ok = 1;
        }
    }
    if (ok && d == 3 && D >= 2) stage2();
    if (ok) print_saved();
    else set_complete();
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    nlo = max(d + 1, best[0] // 2 + 1, int(0.45 * moore) // 2)
    if nlo > moore // 2:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
