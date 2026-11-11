"""Annealed multi-orbit voltage lifts over metacyclic groups.

New idea (not in the parent): a bipartite lift with K fibre orbits per side.
Base vertices are A_0..A_{K-1} and B_0..B_{K-1}. There are d perfect matchings
between the sides, dart i joining A_u to B_{sig_i(u)} with a voltage vol_i(u)
in a group G of order N. Vertex (A_u, g) joins (B_w, g*v), with w = sig_i(u) and
v = vol_i(u). Left multiplication is an automorphism, so the diameter check needs
only one BFS per base vertex, from its identity fibre element.

The search does simulated annealing over voltages and permutations, minimising
the number of (base representative, vertex) pairs at distance more than D. A
state with zero such pairs is verified by full BFS from every vertex, then kept.
The target order climbs in steps of 2 after each success. Budget is spent on the
current target, rotating over K values and groups. Nonabelian groups are sampled
preferentially.
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

#define MAXN 1024
#define MAXK 16
#define MAXDEG 16
#define MAXV 2048
#define MAXGRP 20000
#define T_HI 2.0
#define T_LO 0.05

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
static int ngroups, nab;

/* Nonabelian groups first (count stored in nab), then abelian ones. */
static void enum_groups(int n) {
    ngroups = 0;
    nab = 0;
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
        if (pass == 0) nab = ngroups;
    }
}

static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NG;
static int K;

/* Element (a, b) is coded a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static void build_group(Grp G) {
    int n = G.m * G.k;
    NG = n;
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

static int sig[MAXDEG][MAXK];
static int vol[MAXDEG][MAXK];
static int incU[MAXK][MAXDEG], incI[MAXK][MAXDEG];

static void rebuild_inc(void) {
    int cnt[MAXK];
    for (int w = 0; w < K; w++) cnt[w] = 0;
    for (int i = 0; i < d; i++)
        for (int u = 0; u < K; u++) {
            int w = sig[i][u];
            incU[w][cnt[w]] = u;
            incI[w][cnt[w]] = i;
            cnt[w]++;
        }
}

/* Simplicity condition for A_u: its d pairs (sig_i(u), vol_i(u)) are distinct. */
static int ok_u(int u) {
    for (int i = 0; i < d; i++)
        for (int j = i + 1; j < d; j++)
            if (sig[i][u] == sig[j][u] && vol[i][u] == vol[j][u]) return 0;
    return 1;
}

/* Neighbour i of vertex v. A_u,g = u*NG+g and B_w,h = (K+w)*NG+h. */
static inline int nbr(int v, int i) {
    if (v < K * NG) {
        int u = v / NG, g = v - u * NG;
        return (K + sig[i][u]) * NG + MT[g * NG + vol[i][u]];
    } else {
        int q = v / NG;
        int w = q - K, h = v - q * NG;
        int u = incU[w][i], ii = incI[w][i];
        return u * NG + MT[h * NG + INV[vol[ii][u]]];
    }
}

static void init_state(void) {
    for (int u = 0; u < K; u++) sig[0][u] = u;
    for (int i = 1; i < d; i++) {
        for (int u = 0; u < K; u++) sig[i][u] = u;
        for (int u = K - 1; u > 0; u--) {
            int j = rndint(u + 1);
            int t = sig[i][u];
            sig[i][u] = sig[i][j];
            sig[i][j] = t;
        }
    }
    for (int i = 0; i < d; i++)
        for (int u = 0; u < K; u++) vol[i][u] = rndint(NG);
    for (int u = 0; u < K; u++) {
        int guard = 0;
        while (!ok_u(u)) {
            int i = rndint(d);
            vol[i][u] = rndint(NG);
            if (++guard > 100000) break;
        }
    }
}

/* ---------------------------------------------------------- bad-pair count */

static int vis[MAXV], dst[MAXV], qu[MAXV];
static int stampc = 0;

/* Number of vertices NOT within distance D of src. */
static int bfs_bad(int src) {
    int V = 2 * K * NG;
    stampc++;
    int head = 0, tail = 0;
    vis[src] = stampc;
    dst[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        int dv = dst[v];
        if (dv >= D) continue;
        for (int i = 0; i < d; i++) {
            int x = nbr(v, i);
            if (vis[x] != stampc) {
                vis[x] = stampc;
                dst[x] = dv + 1;
                qu[tail++] = x;
            }
        }
    }
    return V - tail;
}

static int evaluate(void) {
    rebuild_inc();
    int bad = 0;
    for (int r = 0; r < 2 * K; r++) bad += bfs_bad(r * NG);
    return bad;
}

/* ---------------------------------------------------------- annealing */

static int anneal(double until) {
    double t0 = now();
    double span = until - t0;
    if (span < 1e-3) span = 1e-3;
    int cur = evaluate();
    double T = T_HI;
    long it = 0;
    for (;;) {
        if (cur == 0) return 1;
        if ((it & 31) == 0) {
            double t = now();
            if (t >= until) return 0;
            double frac = (t - t0) / span;
            if (frac > 1) frac = 1;
            T = T_HI * pow(T_LO / T_HI, frac);
        }
        it++;
        if (K == 1 || rndint(100) < 70) {
            int i = rndint(d), u = rndint(K);
            int old = vol[i][u];
            int nv = rndint(NG);
            if (nv == old) continue;
            vol[i][u] = nv;
            if (!ok_u(u)) { vol[i][u] = old; continue; }
            int nbad = evaluate();
            int delta = nbad - cur;
            if (delta <= 0 || rnd01() < exp(-delta / T)) cur = nbad;
            else vol[i][u] = old;
        } else {
            int i = 1 + rndint(d - 1);
            int u1 = rndint(K), u2 = rndint(K);
            if (u1 == u2) continue;
            int s1 = sig[i][u1], s2 = sig[i][u2];
            sig[i][u1] = s2;
            sig[i][u2] = s1;
            if (!ok_u(u1) || !ok_u(u2)) {
                sig[i][u1] = s1;
                sig[i][u2] = s2;
                continue;
            }
            int nbad = evaluate();
            int delta = nbad - cur;
            if (delta <= 0 || rnd01() < exp(-delta / T)) cur = nbad;
            else {
                sig[i][u1] = s1;
                sig[i][u2] = s2;
            }
        }
    }
}

/* ---------------------------------------------------------- explicit verify */

static int adjl[MAXV][MAXDEG], degl[MAXV];
static int dd_[MAXV], qq_[MAXV];
static int eu_[16384], ev_[16384];
static int beu[16384], bev[16384];
static int bestV = 0, bestE = 0;

/* Build the explicit simple graph from the current state and check it fully. */
static int build_and_verify(int *eu, int *ev, int *pne) {
    int V = 2 * K * NG;
    int VA = K * NG;
    for (int v = 0; v < V; v++) degl[v] = 0;
    int ne = 0;
    for (int u = 0; u < VA; u++)
        for (int i = 0; i < d; i++) {
            int w = nbr(u, i);
            if (degl[u] >= d || degl[w] >= d) return 0;
            adjl[u][degl[u]++] = w;
            adjl[w][degl[w]++] = u;
            eu[ne] = u;
            ev[ne] = w;
            ne++;
        }
    for (int v = 0; v < V; v++) {
        if (degl[v] != d) return 0;
        for (int i = 0; i < d; i++)
            for (int j = i + 1; j < d; j++)
                if (adjl[v][i] == adjl[v][j]) return 0;
    }
    for (int s = 0; s < V; s++) {
        for (int i = 0; i < V; i++) dd_[i] = -1;
        int head = 0, tail = 0;
        dd_[s] = 0;
        qq_[tail++] = s;
        while (head < tail) {
            int v = qq_[head++];
            if (dd_[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int x = adjl[v][i];
                if (dd_[x] < 0) {
                    dd_[x] = dd_[v] + 1;
                    qq_[tail++] = x;
                }
            }
        }
        if (tail != V) return 0;
    }
    *pne = ne;
    return 1;
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

    if (d < 2 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double t0 = now();
    t_end = t0 + budget * 0.95;

    long mo = moore_bound();
    int Mmax = mo < MAXV ? (int)mo : MAXV;

    double chunk = budget / 12.0;
    if (chunk < 0.8) chunk = 0.8;
    if (chunk > 4.0) chunk = 4.0;

    int T = tlo;
    if (T < 2 * (d + 1)) T = 2 * (d + 1);
    if (T % 2) T++;

    while (now() < t_end && T <= Mmax) {
        int cand[MAXK], nc = 0;
        for (int k = 1; k <= MAXK; k++) {
            if (T % (2 * k)) continue;
            int n = T / (2 * k);
            if (n < d + 1 || n > MAXN) continue;
            cand[nc++] = k;
        }
        if (nc == 0) { T += 2; continue; }
        K = cand[rndint(nc)];
        int n = T / (2 * K);
        enum_groups(n);
        if (ngroups == 0) { T += 2; continue; }
        Grp G = (nab > 0 && rnd01() < 0.8) ? groups[rndint(nab)] : groups[rndint(ngroups)];
        build_group(G);
        init_state();
        double until = now() + chunk;
        if (until > t_end) until = t_end;
        if (anneal(until)) {
            int ne = 0;
            if (build_and_verify(eu_, ev_, &ne)) {
                memcpy(beu, eu_, sizeof(int) * (size_t)ne);
                memcpy(bev, ev_, sizeof(int) * (size_t)ne);
                bestV = 2 * K * NG;
                bestE = ne;
                T = bestV + 2;
            }
        }
    }

    if (bestV > 0) {
        printf("%d %d\n", bestV, bestE);
        for (int e = 0; e < bestE; e++) printf("%d %d\n", beu[e], bev[e]);
    } else {
        printf("0 0\n");
    }
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

    # Lowest total order to attempt: a little under 0.45 of the Moore bound,
    # and above what we already have. Totals are always even.
    tlo = max(best[0] + 2, 2 * (d + 1), (int(0.45 * moore) // 2) * 2)
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
