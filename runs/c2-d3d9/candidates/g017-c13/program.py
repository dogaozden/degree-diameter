"""Bi-Cayley and voltage-lift search over metacyclic groups, with hill climbing.

Family: a base bipartite d-regular multigraph on K + K vertices (K = 1..4) with
voltages in a metacyclic group G = Z_m x| Z_q of order n. The lift has 2*K*n
vertices, A_{i,x} ~ B_{j, x*g} for each dart (i, j, g). Left multiplication is an
automorphism, so the diameter check needs only 2K BFS runs (one per orbit).

Search: for each target order T = 2*K*n (ascending from a lower bound), collect the
candidate (K, group) pairs and run hill climbing on the voltages. The cost is the
number of vertex pairs at distance more than D from the orbit representatives.
A move changes one voltage and is kept if the cost does not increase. A success
is re-verified by BFS from every orbit representative before it is printed.
K = 1 is the old bi-Cayley family. Python keeps the best of the known start and
the C result, and checks everything with lib.is_valid.
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

#define MAXN 1024
#define MAXK 4
#define MAXDEG 16
#define MAXDART (MAXK * MAXDEG)
#define MAXV (2 * MAXK * MAXN)
#define MAXGRP 4096
#define MAXENT 8192
#define STEPS 3000

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

/* ---------------------------------------------------------- groups Z_m x| Z_q */

typedef struct { int m, q, r; } Grp;

/* Metacyclic groups of order n. Nonabelian first, then abelian. Cyclic groups
 * appear once, as (m = n, q = 1, r = 1). */
static int enum_groups(int n, Grp *out, int cap) {
    int c = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 2; m <= n; m++) {
            if (n % m) continue;
            int q = n / m;
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, q, m) != 1 % m) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (c < cap) {
                    out[c].m = m;
                    out[c].q = q;
                    out[c].r = r;
                    c++;
                }
            }
        }
    }
    return c;
}

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NN;

/* Element (a, b) is coded a*q + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod q). */
static void build_group(Grp G) {
    int n = G.m * G.q;
    NN = n;
    static int rp[MAXN];
    rp[0] = 1 % G.m;
    for (int b = 1; b < G.q; b++) rp[b] = (int)((long)rp[b - 1] * G.r % G.m);
    for (int x = 0; x < n; x++) {
        int a = x / G.q, b = x % G.q;
        for (int y = 0; y < n; y++) {
            int c = y / G.q, e = y % G.q;
            MT[x * n + y] = (int)(((long)a + (long)rp[b] * c) % G.m) * G.q + (b + e) % G.q;
        }
    }
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------- base graph and voltages */

static int KB = 1;                       /* base size per side */
static int ti[MAXDART], tj[MAXDART], tg[MAXDART], tinv[MAXDART];
static int Adart[MAXK][MAXDEG];          /* darts leaving A_i */
static int Bdart[MAXK][MAXDEG];          /* darts entering B_j */

static void set_bdarts(void) {
    int cnt[MAXK];
    for (int j = 0; j < MAXK; j++) cnt[j] = 0;
    int nd = KB * d;
    for (int t = 0; t < nd; t++) {
        int j = tj[t];
        Bdart[j][cnt[j]++] = t;
    }
}

/* Random d-regular bipartite base multigraph: A-slots i repeated d times, B-slots shuffled. */
static void random_base(void) {
    int nd = KB * d;
    int bl[MAXDART];
    for (int t = 0; t < nd; t++) {
        ti[t] = t / d;
        bl[t] = t / d;
    }
    for (int t = nd - 1; t > 0; t--) {
        int r = rndint(t + 1);
        int tmp = bl[t]; bl[t] = bl[r]; bl[r] = tmp;
    }
    for (int t = 0; t < nd; t++) tj[t] = bl[t];
    set_bdarts();
}

/* 1 if dart t with voltage g clashes with another dart of the same A vertex
 * (same target B and same voltage), among darts with index < upto. */
static int clash(int t, int g, int upto) {
    int i = ti[t], j = tj[t];
    for (int s = 0; s < d; s++) {
        int t2 = Adart[i][s];
        if (t2 != t && t2 < upto && tj[t2] == j && tg[t2] == g) return 1;
    }
    return 0;
}

static int init_volts(void) {
    int nd = KB * d, n = NN;
    for (int t = 0; t < nd; t++) {
        int placed = 0;
        for (int tr = 0; tr < 400 && !placed; tr++) {
            int g = rndint(n);
            if (!clash(t, g, t)) {
                tg[t] = g;
                tinv[t] = INV[g];
                placed = 1;
            }
        }
        if (!placed) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- cost via implicit lift */

static int dist_[MAXV], queue_[MAXV];

/* Number of vertices within distance D of src in the implicit lift.
 * Vertices A_{i,x} = i*n + x, B_{j,y} = KB*n + j*n + y. */
static int bfs_reach(int src) {
    int n = NN, V = 2 * KB * n, An = KB * n;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < An) {
            int i = v / n, x = v % n;
            for (int s = 0; s < d; s++) {
                int t = Adart[i][s];
                int u = An + tj[t] * n + MT[x * n + tg[t]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int w = v - An, j = w / n, y = w % n;
            for (int s = 0; s < d; s++) {
                int t = Bdart[j][s];
                int u = ti[t] * n + MT[y * n + tinv[t]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Total number of unreached pairs over the 2K orbit representatives. */
static int cost(void) {
    int n = NN, V = 2 * KB * n, An = KB * n, total = 0;
    for (int i = 0; i < KB; i++) total += V - bfs_reach(i * n);
    for (int j = 0; j < KB; j++) total += V - bfs_reach(An + j * n);
    return total;
}

/* ---------------------------------------------------------- hill climbing */

static Grp curG;

/* One restart: random base, random voltages, then voltage moves that do not raise the cost.
 * Returns 1 when cost reaches 0 (the state is left as the solution). */
static int hill(Grp G, double until) {
    build_group(G);
    curG = G;
    random_base();
    if (!init_volts()) return 0;
    int c = cost();
    for (int step = 0; step < STEPS && c > 0; step++) {
        if ((step & 15) == 0 && now() >= until) break;
        int nd = KB * d, n = NN;
        int t = rndint(nd), g = rndint(n);
        if (g == tg[t] || clash(t, g, nd)) continue;
        int og = tg[t], oi = tinv[t];
        tg[t] = g;
        tinv[t] = INV[g];
        int nc = cost();
        if (nc <= c) c = nc;
        else { tg[t] = og; tinv[t] = oi; }
    }
    return c == 0;
}

/* ---------------------------------------------------------- scan over orders */

typedef struct { int K; Grp G; } Entry;
static Entry ents[MAXENT];
static int nent;
static Grp tmpg[MAXGRP];

static void collect(int T) {
    nent = 0;
    int half = T / 2;
    for (int K = 1; K <= MAXK; K++) {
        if (half % K) continue;
        int n = half / K;
        if (n < 2 || n > MAXN - 1) continue;
        if (d > K * n) continue;
        int c = enum_groups(n, tmpg, MAXGRP);
        for (int e = 0; e < c && nent < MAXENT; e++) {
            ents[nent].K = K;
            ents[nent].G = tmpg[e];
            nent++;
        }
    }
}

static int bestT = 0, bestK = 0;
static Grp bestG;
static int bTj[MAXDART], bTg[MAXDART];

static void record(int T) {
    bestT = T;
    bestK = KB;
    bestG = curG;
    int nd = KB * d;
    for (int t = 0; t < nd; t++) {
        bTj[t] = tj[t];
        bTg[t] = tg[t];
    }
}

/* Round-robin over candidate (K, group) pairs for order T until the slice ends. */
static int search_T(int T, double until) {
    collect(T);
    if (nent == 0) return 0;
    while (now() < until) {
        for (int e = 0; e < nent && now() < until; e++) {
            KB = ents[e].K;
            if (hill(ents[e].G, until)) {
                record(T);
                return 1;
            }
        }
    }
    return 0;
}

/* ---------------------------------------------------------- explicit graph */

static int adjl[MAXV][MAXDEG], degl[MAXV];

static void add_e(int u, int v) {
    adjl[u][degl[u]++] = v;
    adjl[v][degl[v]++] = u;
}

static int dd_[MAXV], qq_[MAXV];

/* Degree check plus BFS from each orbit representative (valid by left-multiplication symmetry). */
static int verify_sources(int V) {
    int n = NN, An = KB * n;
    for (int v = 0; v < V; v++) if (degl[v] != d) return 0;
    for (int s = 0; s < 2 * KB; s++) {
        int src = (s < KB) ? s * n : An + (s - KB) * n;
        for (int v = 0; v < V; v++) dd_[v] = -1;
        int head = 0, tail = 0;
        dd_[src] = 0;
        qq_[tail++] = src;
        while (head < tail) {
            int v = qq_[head++];
            if (dd_[v] >= D) continue;
            for (int k = 0; k < degl[v]; k++) {
                int u = adjl[v][k];
                if (dd_[u] < 0) { dd_[u] = dd_[v] + 1; qq_[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void set_complete(void) {
    int V = 2 * d;
    for (int v = 0; v < V; v++) degl[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_e(a, d + b);
    printf("%d %d\n", V, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
}

static void print_explicit(int V) {
    long m = 0;
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) m++;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int i = 0; i < degl[u]; i++)
            if (u < adjl[u][i]) printf("%d %d\n", u, adjl[u][i]);
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget tlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int tlo = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }
    for (int i = 0; i < MAXK; i++)
        for (int s = 0; s < d; s++) Adart[i][s] = i * d + s;

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    long tmax = moore;
    if (tmax > 2L * MAXK * (MAXN - 1)) tmax = 2L * MAXK * (MAXN - 1);
    int T0 = tlo;
    if (T0 < 4) T0 = 4;
    if (T0 & 1) T0++;

    double per = budget / 30.0;
    if (per < 0.4) per = 0.4;
    if (per > 2.5) per = 2.5;

    if (d >= 2 && D >= 2) {
        for (long T = T0; T <= tmax && now() < t_end; T += 2) {
            double until = now() + per;
            if (until > t_end) until = t_end;
            search_T((int)T, until);
        }
    }

    int ok = 0;
    if (bestT > 0) {
        KB = bestK;
        build_group(bestG);
        int n = NN, nd = KB * d, V = 2 * KB * n, An = KB * n;
        for (int t = 0; t < nd; t++) {
            tj[t] = bTj[t];
            tg[t] = bTg[t];
            ti[t] = t / d;
            tinv[t] = INV[tg[t]];
        }
        set_bdarts();
        for (int v = 0; v < V; v++) degl[v] = 0;
        for (int t = 0; t < nd; t++) {
            int i = ti[t], j = tj[t], g = tg[t];
            for (int x = 0; x < n; x++)
                add_e(i * n + x, An + j * n + MT[x * n + g]);
        }
        ok = verify_sources(V);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Lower bound on the total order to scan from: never below what we already have,
    # and well below the frontier so easy orders succeed quickly.
    tlo = max(best[0] + 2, int(0.45 * moore))
    if tlo > moore:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), tlo],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
