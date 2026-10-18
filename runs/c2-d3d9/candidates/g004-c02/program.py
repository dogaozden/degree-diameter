"""Bold variant: random lifts of small bipartite base graphs over finite groups.

Construction: pick b base vertices per side and a random d-regular bipartite
multigraph on them (configuration model). Give each dart a voltage g in a
group G of order N. The lift has parts U_u x G and W_w x G, with (u,x) ~ (w, x*g)
for each dart (u,w,g). Vertices have degree d and the lift is bipartite by
construction. Left multiplication is an automorphism, so distances from (u,x)
equal distances from (u,1). The diameter cost therefore needs only 2b BFS runs.

The search runs in C. It scans orders V = 2bN upward from the known start, and
for each V tries random (b, N, metacyclic group) choices with local search on
the voltages and the W-side stub matching. A cost of 0 means diameter <= D and
no multi-edges. Every success is re-verified with a full BFS before it is
kept. If nothing beats the start, the program prints "0 0" and Python keeps
the valid start graph. Python checks the final graph with lib.is_valid.
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

#define MAXN 2048
#define MAXV 4096
#define MAXDEG 16
#define MAXGRP 4096
#define MAXDART 512

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

/* ---------------------------------------------------------- groups Z_m x| Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

/* All metacyclic groups of order N: element (a,b) coded a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void enum_groups(int N) {
    ngroups = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (ngroups < MAXGRP) { groups[ngroups].m = 1; groups[ngroups].k = k; groups[ngroups].r = 0; ngroups++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXGRP) { groups[ngroups].m = m; groups[ngroups].k = k; groups[ngroups].r = r; ngroups++; }
        }
    }
}

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;

static void build_group(Grp G) {
    int n = G.m * G.k;
    NN = n;
    static int rp[MAXN];
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

static int bb;                       /* base vertices per side */
static int dwv[MAXDART], gvv[MAXDART]; /* dart i: U-vertex i/d, W-vertex dwv[i], voltage gvv[i] */
static int ADJ[MAXV * MAXDEG];
static int cntv[MAXV];
static int dist_[MAXV], q_[MAXV];

/* U vertex (u,x) = u*NN + x; W vertex (w,y) = bb*NN + w*NN + y.
 * Dart (u,w,g) joins (u,x) to (w, x*g). */
static void build_adj(void) {
    int n = NN, V = 2 * bb * n;
    for (int v = 0; v < V; v++) cntv[v] = 0;
    int nd = d * bb;
    for (int i = 0; i < nd; i++) {
        int u = i / d, w = dwv[i], g = gvv[i];
        for (int x = 0; x < n; x++) {
            int a = u * n + x;
            int c = bb * n + w * n + MT[x * n + g];
            ADJ[a * MAXDEG + cntv[a]++] = c;
            ADJ[c * MAXDEG + cntv[c]++] = a;
        }
    }
}

/* Number of pairs of darts giving the same lift edges (same u, w and voltage). */
static int count_dups(void) {
    int nd = d * bb, c = 0;
    for (int i = 0; i < nd; i++)
        for (int j = i + 1; j < nd; j++)
            if (i / d == j / d && dwv[i] == dwv[j] && gvv[i] == gvv[j]) c++;
    return c;
}

/* Cost = number of (base representative, vertex) pairs at distance > D.
 * By left-multiplication symmetry, one BFS per fibre suffices. */
static long eval_cost(void) {
    int n = NN, V = 2 * bb * n;
    int dup = count_dups();
    if (dup) return (long)dup * V * 8 + V;
    build_adj();
    long cost = 0;
    for (int r = 0; r < 2 * bb; r++) {
        int src = (r < bb) ? r * n : bb * n + (r - bb) * n;
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[src] = 0;
        q_[t++] = src;
        while (h < t) {
            int v = q_[h++];
            if (dist_[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = ADJ[v * MAXDEG + k];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; q_[t++] = u; }
            }
        }
        cost += V - t;
    }
    return cost;
}

/* Full verification: simple, and every vertex reaches all others within D. */
static int verify_full(void) {
    int n = NN, V = 2 * bb * n;
    if (count_dups()) return 0;
    build_adj();
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dist_[v] = -1;
        int h = 0, t = 0;
        dist_[s] = 0;
        q_[t++] = s;
        while (h < t) {
            int v = q_[h++];
            if (dist_[v] >= D) continue;
            for (int k = 0; k < d; k++) {
                int u = ADJ[v * MAXDEG + k];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; q_[t++] = u; }
            }
        }
        if (t != V) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- search */

static int bestV = 0, bestb = 0, bestN = 0;
static Grp bestG;
static int bestdw[MAXDART], bestgv[MAXDART];

/* One local-search attempt for base size b_ and group order N_. Returns 1 on success. */
static int attempt(int b_, int N_, double until) {
    bb = b_;
    enum_groups(N_);
    if (ngroups == 0) return 0;
    Grp G = groups[rndint(ngroups)];
    build_group(G);
    int nd = d * bb;
    for (int i = 0; i < nd; i++) { dwv[i] = i / d; gvv[i] = rndint(N_); }
    for (int i = nd - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = dwv[i]; dwv[i] = dwv[j]; dwv[j] = t;
    }
    long cur = eval_cost();
    int steps = 0;
    while (cur > 0 && steps < 4000) {
        if ((steps & 63) == 0 && now() >= until) break;
        steps++;
        int i = rndint(nd), j = rndint(nd);
        int oig = gvv[i], oiw = dwv[i], ojg = gvv[j], ojw = dwv[j];
        if (rndint(2) == 0) {
            gvv[i] = rndint(N_);
        } else {
            int t = dwv[i]; dwv[i] = dwv[j]; dwv[j] = t;
        }
        long c = eval_cost();
        if (c <= cur) {
            cur = c;
        } else {
            gvv[i] = oig; dwv[i] = oiw; gvv[j] = ojg; dwv[j] = ojw;
        }
    }
    if (cur != 0) return 0;
    if (!verify_full()) return 0;
    int V = 2 * bb * NN;
    if (V > bestV) {
        bestV = V;
        bestb = bb;
        bestN = NN;
        bestG = G;
        for (int i = 0; i < nd; i++) { bestdw[i] = dwv[i]; bestgv[i] = gvv[i]; }
    }
    return 1;
}

static void print_best(void) {
    bb = bestb;
    build_group(bestG);
    int nd = d * bb;
    for (int i = 0; i < nd; i++) { dwv[i] = bestdw[i]; gvv[i] = bestgv[i]; }
    build_adj();
    int V = 2 * bb * NN;
    printf("%d %d\n", V, V * d / 2);
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++) {
            int u = ADJ[v * MAXDEG + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed budget vstart vmax\n", argv[0]);
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int vstart = atoi(argv[5]);
    int vmax = atoi(argv[6]);

    if (d < 2 || d > MAXDEG || D < 2 || vmax < 4 || vmax > MAXV) {
        printf("0 0\n");
        return 0;
    }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + budget * 0.9;

    if (vstart < 4) vstart = 4;
    if (vstart & 1) vstart++;
    if (vmax & 1) vmax--;

    for (int V = vstart; V <= vmax && now() < t_end; V += 2) {
        int ob[16], on[16], no = 0;
        for (int b = 1; b <= 8; b++) {
            if (V % (2 * b)) continue;
            int N = V / (2 * b);
            if (N < 2 || N > MAXN) continue;
            ob[no] = b;
            on[no] = N;
            no++;
        }
        if (no == 0) continue;
        int remaining = (vmax - V) / 2 + 1;
        double untilV = now() + (t_end - now()) / remaining;
        while (now() < untilV) {
            int o = rndint(no);
            double until = now() + 0.05;
            if (until > untilV) until = untilV;
            if (attempt(ob[o], on[o], until)) break;
        }
    }

    if (bestV == 0) {
        printf("0 0\n");
        return 0;
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
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d} fallback
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 2.0:
        return best

    vmax = min(moore, 4000)
    vmax -= vmax % 2
    # Scan upward from just above the current best, so cheap small orders
    # succeed quickly and leave time for the hard range near the record.
    vstart = best[0] + 2
    if vstart % 2:
        vstart += 1
    if vstart > vmax:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vstart, vmax],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
