"""Combined bipartite degree-diameter search, v3.

Phase 1 (bi-Cayley): one vertex per side over a group G of order N, with
A_x ~ B_{x*s} for s in S (0 in S). Groups are all semidirect products Z_m x| Z_k
(nonabelian and abelian). Each round scans N upward and samples connection sets;
for d = 3 this covers {0,a,b} over every group. Left multiplication is an
automorphism, so two BFS runs (from A_e and B_e) decide diameter.

Phase 2 (fibre lifts): p fibres per side (p = 1..3), a random d-regular base
multigraph on p+p vertices, and Z-voltages in G. Hill climbing minimises the
number of pairs at distance > D, computed from the 2p fibre representatives only.

Every candidate that beats the current best is re-verified by full BFS from
every vertex before it is stored. Python starts from K_{d,d} or an algebraic
graph (projective plane, Araujo-Pardo-Lopez, W(q)), passes its order to C, and
keeps the C result only if lib.is_valid accepts it.
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

#define MAXN 512
#define MAXV (6 * MAXN)
#define MAXD 16
#define MAXP 3
#define MAXDARTS (MAXP * MAXD)
#define MAXGRP 256
#define SAMPLES 300
#define STEPS 1500

static int d, D;
static int needV = 0, bestV = 0;
static int SB = 0;   /* A-side vertices are [0, SB) */

static int deg[MAXV];
static int adj[MAXV][MAXD];
static int bestDeg[MAXV];
static int bestAdj[MAXV][MAXD];

static int dist_[MAXV], q_[MAXV];
static int MT[MAXN * MAXN];

typedef struct { int m, k, r; } Grp;
static Grp glist[MAXGRP];
static int nglist = 0;

static int nd = 0;
static int dI[MAXDARTS], dJ[MAXDARTS], dG[MAXDARTS];
static int S_[MAXD];

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

/* Largest possible number of vertices for max degree d and diameter D. */
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

static int maxN(void) {
    long nm = moore_bound() / 2;
    if (nm > MAXN - 1) nm = MAXN - 1;
    return (int)nm;
}

static int curV(void) { return bestV > needV ? bestV : needV; }

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void list_groups(int N) {
    nglist = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (nglist < MAXGRP) {
                glist[nglist].m = 1; glist[nglist].k = k; glist[nglist].r = 0;
                nglist++;
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (nglist < MAXGRP) {
                glist[nglist].m = m; glist[nglist].k = k; glist[nglist].r = r;
                nglist++;
            }
        }
    }
}

static void build_group(int N, Grp G) {
    int m = G.m, k = G.k;
    static int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

/* ------------------------------------------------------------ graph core */

static void gadd(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static int bfs_count(int V, int src) {
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    q_[tail++] = src;
    while (head < tail) {
        int v = q_[head++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                q_[tail++] = u;
            }
        }
    }
    return tail;
}

/* Full check: degrees in [1, d], simple, bipartite w.r.t. SB, diameter <= D. */
static int verify_full(int V) {
    for (int v = 0; v < V; v++) {
        if (deg[v] < 1 || deg[v] > d) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u < 0 || u >= V || u == v) return 0;
            if ((v < SB) == (u < SB)) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < V; s++)
        if (bfs_count(V, s) != V) return 0;
    return 1;
}

static int try_save(int V) {
    if (V <= curV()) return 0;
    if (!verify_full(V)) return 0;
    bestV = V;
    for (int v = 0; v < V; v++) {
        bestDeg[v] = deg[v];
        for (int i = 0; i < deg[v]; i++) bestAdj[v][i] = adj[v][i];
    }
    return 1;
}

static void print_best(void) {
    long m = 0;
    for (int v = 0; v < bestV; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) m++;
    printf("%d %ld\n", bestV, m);
    for (int v = 0; v < bestV; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
}

/* ------------------------------------------------------------ phase 1: bi-Cayley */

static void pick_S(int N) {
    S_[0] = 0;
    for (int t = 1; t < d; t++) {
        for (;;) {
            int x = 1 + rndint(N - 1);
            int dup = 0;
            for (int j = 0; j < t; j++)
                if (S_[j] == x) { dup = 1; break; }
            if (!dup) { S_[t] = x; break; }
        }
    }
}

/* A-vertex x ~ B-vertex x*s for s in S. Vertex A_x = x, B_y = N + y. */
static void build_bicayley(int N, const int *S, int nt) {
    SB = N;
    for (int v = 0; v < 2 * N; v++) deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < nt; t++)
            gadd(x, N + MT[x * N + S[t]]);
}

static int test_bicayley(int N) {
    build_bicayley(N, S_, d);
    int V = 2 * N;
    if (bfs_count(V, 0) != V) return 0;
    if (bfs_count(V, N) != V) return 0;
    return try_save(V);
}

static void phase1(double until) {
    int nmax = maxN();
    if (nmax < d + 1) return;
    while (now() < until) {
        for (int N = d + 1; N <= nmax && now() < until; N++) {
            if (2 * N <= curV()) continue;
            list_groups(N);
            int done = 0;
            for (int gi = 0; gi < nglist && !done && now() < until; gi++) {
                build_group(N, glist[gi]);
                for (int s = 0; s < SAMPLES && !done; s++) {
                    if ((s & 63) == 0 && now() >= until) break;
                    pick_S(N);
                    if (test_bicayley(N)) done = 1;
                }
            }
        }
    }
}

/* ------------------------------------------------------------ phase 2: fibre lifts */

static int connected_base(int p, int M[MAXP][MAXP]) {
    int par[2 * MAXP];
    for (int i = 0; i < 2 * p; i++) par[i] = i;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (M[i][j]) {
                int a = i, b = p + j;
                while (par[a] != a) a = par[a];
                while (par[b] != b) b = par[b];
                if (a != b) par[a] = b;
            }
    int r0 = 0;
    while (par[r0] != r0) r0 = par[r0];
    for (int i = 0; i < 2 * p; i++) {
        int a = i;
        while (par[a] != a) a = par[a];
        if (a != r0) return 0;
    }
    return 1;
}

static int clash_g(int t, int g) {
    for (int t2 = 0; t2 < nd; t2++)
        if (t2 != t && dI[t2] == dI[t] && dJ[t2] == dJ[t] && dG[t2] == g) return 1;
    return 0;
}

/* Random connected p x p base with row and column sums d; random distinct voltages per block. */
static void make_base(int p, int N) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        if (connected_base(p, M)) break;
    }
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dI[nd] = i; dJ[nd] = j; dG[nd] = -1;
                nd++;
            }
    for (int t = 0; t < nd; t++) {
        for (;;) {
            int g = rndint(N);
            if (!clash_g(t, g)) { dG[t] = g; break; }
        }
    }
}

/* A fibre i, element x -> i*N + x. B fibre j, element y -> (p+j)*N + y.
 * Dart (i, j, g): A(i,x) ~ B(j, x*g). */
static void build_lift(int p, int N) {
    SB = p * N;
    for (int v = 0; v < 2 * p * N; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            gadd(dI[t] * N + x, (p + dJ[t]) * N + MT[x * N + dG[t]]);
}

/* Number of (vertex, pair) misses from the 2p fibre representatives.
 * Exact by left-multiplication symmetry. */
static long orbit_bad(int p, int N) {
    int V = 2 * p * N;
    long bad = 0;
    for (int u = 0; u < 2 * p; u++)
        bad += V - bfs_count(V, u * N);
    return bad;
}

static void lift_search(int p, int N, double until) {
    if (N < d || N > MAXN - 1 || 2 * p * N > MAXV) return;
    list_groups(N);
    if (nglist == 0) return;
    build_group(N, glist[rndint(nglist)]);
    make_base(p, N);
    build_lift(p, N);
    long bad = orbit_bad(p, N);
    for (int s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 63) == 0 && now() >= until) return;
        int t = rndint(nd);
        int g = rndint(N);
        if (g == dG[t] || clash_g(t, g)) continue;
        int old = dG[t];
        dG[t] = g;
        build_lift(p, N);
        long nb = orbit_bad(p, N);
        if (nb <= bad || rnd01() < 0.01) {
            bad = nb;
        } else {
            dG[t] = old;
            build_lift(p, N);
        }
    }
    if (bad == 0) {
        build_lift(p, N);
        try_save(2 * p * N);
    }
}

static int lift_ok(int p) {
    long hi = moore_bound() / (2 * p);
    if (hi > MAXN - 1) hi = MAXN - 1;
    long lo = curV() / (2 * p) + 1;
    if (lo < d) lo = d;
    return hi >= lo;
}

static void phase2(double until) {
    while (now() < until) {
        int cand[MAXP], nc = 0;
        for (int p = 1; p <= MAXP; p++)
            if (lift_ok(p)) cand[nc++] = p;
        if (nc == 0) return;
        int p = cand[rndint(nc)];
        long lo = curV() / (2 * p) + 1;
        if (lo < d) lo = d;
        long hi = moore_bound() / (2 * p);
        if (hi > MAXN - 1) hi = MAXN - 1;
        long span = hi - lo + 1;
        if (span > 6) span = 6;
        int N = (int)lo + rndint((int)span);
        lift_search(p, N, until);
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed budget [start_vertices]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    needV = argc > 5 ? atoi(argv[5]) : 0;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double span = budget * 0.92;
    double t_end = t0 + span;

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    phase1(t0 + span * 0.5);
    phase2(t_end);
    if (bestV > 0) print_best();
    else printf("0 0\n");
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
        q = _largest_prime_power_le(min(d - 1, 4))
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass  # keep the valid fallback
    return best
