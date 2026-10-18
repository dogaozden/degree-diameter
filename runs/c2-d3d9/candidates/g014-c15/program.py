"""Bold variant: random bipartite voltage lifts over metacyclic groups, found by annealing.

Base graph: nb vertices per side, d perfect matchings between the sides (parallel darts
allowed). Each dart carries a voltage in a group G of order N, so the lift has 2*nb*N vertices
and is d-regular and bipartite. Left multiplication by G is an automorphism, so the diameter
only needs BFS from one representative per base vertex. nb = 1 is the bi-Cayley family used by
the parent. Larger nb gives other orders and structures.

C side: simulated annealing over voltages and matching swaps, with cost = number of vertices not
within D of the representatives (plus a large penalty for parallel darts with equal voltage).
Groups of order N are scanned per base size, and the search keeps the largest total order
reached. Before printing, the lift is re-verified with a BFS from every vertex. If nothing is
found, the C program prints K_{d,d}.

Python: a cheap cyclic Haar fallback, then the C run. Results are checked with lib.is_valid,
and the largest valid graph is returned.
"""
import random
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1100
#define MAXB 12
#define MAXDEG 16
#define MAXV 2400
#define MAXGRP 8192

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

/* Largest possible total order of a bipartite graph with max degree d and diameter D. */
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

/* ---------------------------------------------------------- groups Z_m x|_r Z_k */

typedef struct { int m, k, r; } Grp;
static Grp groups[MAXGRP];
static int ngroups;

static void add_group(int m, int k, int r) {
    if (ngroups < MAXGRP) {
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        ngroups++;
    }
}

static void enum_groups(int N) {
    ngroups = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) { add_group(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_group(m, k, r);
        }
    }
}

static int MT[MAXG * MAXG];  /* MT[x*NG + y] = x*y, element (a,b) coded a*k+b, identity 0 */
static int INV[MAXG];
static int NG;

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
    for (int x = 0; x < n; x++) {
        for (int y = 0; y < n; y++) {
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
        }
    }
}

/* ---------------------------------------------------------- lift configuration */

typedef struct {
    int nb, N;
    Grp G;
    int sig[MAXDEG][MAXB];   /* A_u ~ B_{sig[i][u]} through matching i */
    int sinv[MAXDEG][MAXB];  /* inverse of sig[i]: B_v ~ A_{sinv[i][v]} */
    int gv[MAXDEG][MAXB];    /* voltage of dart (i,u) */
    int gi[MAXDEG][MAXB];    /* inverse voltage */
} Config;

static Config cfg, bst;
static int bestTotal = 0;

static void random_perm(int *p, int n) {
    for (int i = 0; i < n; i++) p[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = p[i]; p[i] = p[j]; p[j] = t;
    }
}

static void init_config(int nb_, Grp G) {
    cfg.nb = nb_;
    cfg.G = G;
    cfg.N = G.m * G.k;
    build_group(G);
    for (int i = 0; i < d; i++) {
        int p[MAXB];
        random_perm(p, nb_);
        for (int u = 0; u < nb_; u++) {
            cfg.sig[i][u] = p[u];
            cfg.sinv[i][p[u]] = u;
        }
        for (int u = 0; u < nb_; u++) {
            int g = rndint(cfg.N);
            cfg.gv[i][u] = g;
            cfg.gi[i][u] = INV[g];
        }
    }
}

/* Number of pairs of darts from the same A-vertex with the same endpoint and voltage. */
static int conflicts(void) {
    int c = 0;
    for (int u = 0; u < cfg.nb; u++)
        for (int i = 0; i < d; i++)
            for (int j = i + 1; j < d; j++)
                if (cfg.sig[i][u] == cfg.sig[j][u] && cfg.gv[i][u] == cfg.gv[j][u]) c++;
    return c;
}

/* ---------------------------------------------------------- BFS on the lift */

/* A_(u,x) has index u*N+x. B_(v,y) has index nb*N + v*N + y.
 * A_(u,x) ~ B_(sig[i][u], x*g_{iu}); B_(v,y) ~ A_(sinv[i][v], y*g_{i,sinv}^{-1}). */
static int dist_[MAXV], que_[MAXV];

static int reach_count(int src) {
    int nN = cfg.N, nb_ = cfg.nb, V = 2 * nb_ * nN, off = nb_ * nN;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    que_[tail++] = src;
    while (head < tail) {
        int w = que_[head++];
        int dw = dist_[w];
        if (dw >= D) continue;
        if (w < off) {
            int u = w / nN, x = w - u * nN;
            for (int i = 0; i < d; i++) {
                int y = MT[x * nN + cfg.gv[i][u]];
                int z = off + cfg.sig[i][u] * nN + y;
                if (dist_[z] < 0) { dist_[z] = dw + 1; que_[tail++] = z; }
            }
        } else {
            int w2 = w - off;
            int v = w2 / nN, y = w2 - v * nN;
            for (int i = 0; i < d; i++) {
                int u = cfg.sinv[i][v];
                int x = MT[y * nN + cfg.gi[i][u]];
                int z = u * nN + x;
                if (dist_[z] < 0) { dist_[z] = dw + 1; que_[tail++] = z; }
            }
        }
    }
    return tail;
}

/* Cost 0 iff the lift is simple and has diameter <= D (all sources are orbit representatives). */
static long eval_cost(void) {
    int nN = cfg.N, nb_ = cfg.nb, V = 2 * nb_ * nN;
    int c = conflicts();
    if (c) return (long)c * V + V;
    long tot = 0;
    for (int u = 0; u < nb_; u++) tot += V - reach_count(u * nN);
    for (int v = 0; v < nb_; v++) tot += V - reach_count((nb_ + v) * nN);
    return tot;
}

static void mutate(void) {
    int i = rndint(d), u = rndint(cfg.nb);
    if (cfg.nb > 1 && rndint(8) == 0) {
        int u2 = rndint(cfg.nb - 1);
        if (u2 >= u) u2++;
        int a = cfg.sig[i][u], b = cfg.sig[i][u2];
        cfg.sig[i][u] = b;
        cfg.sig[i][u2] = a;
        cfg.sinv[i][b] = u;
        cfg.sinv[i][a] = u2;
    } else {
        int g = rndint(cfg.N);
        cfg.gv[i][u] = g;
        cfg.gi[i][u] = INV[g];
    }
}

/* Anneal for base size nb_ and group order N_ until `until`. On success cfg holds a valid lift. */
static int search_config(int nb_, int N_, double until) {
    enum_groups(N_);
    if (ngroups == 0) return 0;
    while (now() < until) {
        int pick = rndint(ngroups);
        if (rnd01() < 0.7) {
            for (int t = 0; t < 30; t++) {
                int c = rndint(ngroups);
                if (groups[c].m > 1 && groups[c].r != 1) { pick = c; break; }
            }
        }
        init_config(nb_, groups[pick]);
        long cost = eval_cost();
        if (cost == 0) return 1;
        long bestc = cost;
        long stale = 0;
        while (now() < until) {
            for (int it = 0; it < 400; it++) {
                Config save;
                memcpy(&save, &cfg, sizeof(Config));
                mutate();
                long c = eval_cost();
                int acc = (c <= cost) || (rnd01() < exp(-(double)(c - cost) / 1.5));
                if (acc) {
                    cost = c;
                    if (cost == 0) return 1;
                    if (cost < bestc) { bestc = cost; stale = 0; }
                    else stale++;
                } else {
                    memcpy(&cfg, &save, sizeof(Config));
                    stale++;
                }
            }
            if (stale > 30000) break;
        }
    }
    return 0;
}

static void record_best(void) {
    int total = 2 * cfg.nb * cfg.N;
    if (total > bestTotal) {
        bestTotal = total;
        bst = cfg;
    }
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);

    if (d < 1 || d > MAXDEG) { printf("0 0\n"); return 0; }

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();

    if (d >= 2 && D >= 2) {
        static const int bopts[8] = {1, 2, 3, 4, 5, 6, 8, 10};
        long Nnext[8];
        int fails[8], inited[8];
        for (int i = 0; i < 8; i++) { Nnext[i] = 0; fails[i] = 0; inited[i] = 0; }
        double slice = budget / 40.0;
        if (slice < 0.4) slice = 0.4;
        if (slice > 2.0) slice = 2.0;

        while (now() < t_end) {
            int attempted = 0;
            for (int oi = 0; oi < 8 && now() < t_end; oi++) {
                int b = bopts[oi];
                long maxN = moore / (2L * b);
                if (maxN > (long)MAXV / (2L * b)) maxN = (long)MAXV / (2L * b);
                if (maxN > MAXG - 1) maxN = MAXG - 1;
                if (maxN < d + 1) continue;
                long lowN = (long)ceil(0.45 * (double)moore / (2.0 * b));
                if (lowN < d + 1) lowN = d + 1;
                long need = (long)bestTotal / (2L * b) + 1;
                if (!inited[oi]) { Nnext[oi] = lowN; inited[oi] = 1; }
                if (Nnext[oi] < need) Nnext[oi] = need;
                if (Nnext[oi] > maxN) continue;

                double s = slice * (1 + (fails[oi] < 3 ? fails[oi] : 3));
                double until = now() + s;
                if (until > t_end) until = t_end;
                attempted = 1;
                int ok = search_config(b, (int)Nnext[oi], until);
                if (ok) {
                    record_best();
                    Nnext[oi]++;
                    fails[oi] = 0;
                } else {
                    fails[oi]++;
                }
            }
            if (!attempted) break;
        }
    }

    if (bestTotal > 0) {
        cfg = bst;
        build_group(cfg.G);
        int nN = cfg.N, nb_ = cfg.nb, V = 2 * nb_ * nN, off = nb_ * nN;
        int good = (V <= MAXV) && (conflicts() == 0);
        for (int w = 0; good && w < V; w++)
            if (reach_count(w) != V) good = 0;
        if (good) {
            printf("%d %d\n", V, nb_ * nN * d);
            for (int u = 0; u < nb_; u++)
                for (int x = 0; x < nN; x++)
                    for (int i = 0; i < d; i++) {
                        int y = MT[x * nN + cfg.gv[i][u]];
                        int v = cfg.sig[i][u];
                        printf("%d %d\n", u * nN + x, off + v * nN + y);
                    }
            return 0;
        }
    }

    /* Fallback: K_{d,d}, always valid for D >= 2. */
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
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


def _haar_fallback(d, D, seed, deadline):
    """Cheap safe fallback: random cyclic Haar graphs, largest order first. Returns (n, edges) or None."""
    rng = random.Random(seed)
    hi = lib.moore_bound(d, D) // 2
    lo = max(d + 1, int(0.4 * hi))
    for n in range(hi, lo - 1, -1):
        for _ in range(2):
            if time.monotonic() > deadline:
                return None
            S = [0] + rng.sample(range(1, n), d - 1)
            V, edges = lib.haar_graph(n, S)
            if lib.is_valid(V, edges, d, D):
                return V, edges
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    start = known_start(d, D)
    best = start if start is not None else lib.haar_graph(d, range(d))   # K_{d,d}
    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    if start is None:
        fb = _haar_fallback(d, D, seed, t0 + 0.06 * time_limit)
        if fb is not None and fb[0] > best[0]:
            best = fb

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass   # keep the valid fallback
    return best
