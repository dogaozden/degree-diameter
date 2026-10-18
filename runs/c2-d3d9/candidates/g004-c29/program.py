"""Multi-base voltage lifts searched by simulated annealing.

Parent family: bi-Cayley graphs (one base vertex per side, d parallel darts), sampled
at random. This program generalises that in two ways.

1. Base graphs with a vertices per side. Any d-regular bipartite multigraph on a+a
   vertices is a union of d perfect matchings (Konig), so the base is given by d
   permutations dest[k] of {0..a-1} with dest[0] = identity, plus a voltage
   volt[k][i] in a group G of order N. The lift has V = 2aN vertices and is d-regular:
   A(i,x) ~ B(dest[k][i], x * volt[k][i]).
2. Simulated annealing over permutations and voltages. The cost is the number of
   (source, vertex) pairs at distance > D, where the sources are the 2a orbit
   representatives A(i,1), B(j,1). Left multiplication by G is an automorphism that acts
   regularly on each side, so these 2a BFS runs give exact diameter information. A
   duplicate-edge penalty keeps the graph simple.

The C engine scans (a, N) candidates with 2aN >= vstart in increasing order of V, tries
the metacyclic groups Z_m x| Z_k of order N, and keeps the largest order that succeeds.
Before printing, it re-verifies the graph with a full BFS from every vertex. If nothing
is found it prints K_{d,d}. Python keeps the best of the known start and the C result
and checks everything with lib.is_valid.
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

#define MAXN 512
#define MAXV 1024
#define MAXA 6
#define MAXD 8
#define MAXGRP 4096
#define MAXCAND 4096
#define MAXE 4096

static int d, D, a, N, V;
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

static int gcd(int x, int y) {
    while (y) { int t = x % y; x = y; y = t; }
    return x;
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

static void add_group(int m, int k, int r) {
    if (ngroups < MAXGRP) {
        groups[ngroups].m = m;
        groups[ngroups].k = k;
        groups[ngroups].r = r;
        ngroups++;
    }
}

static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) { add_group(1, k, 0); continue; }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_group(m, k, r);
        }
    }
}

static void shuffle_groups(void) {
    for (int i = ngroups - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Grp t = groups[i];
        groups[i] = groups[j];
        groups[j] = t;
    }
}

static int MT[MAXN * MAXN];  /* multiplication table, index x*N + y */
static int INV[MAXN];

/* Element (x1, b) coded x1*k + b; (x1,b)(c,e) = (x1 + r^b c mod m, b + e mod k). Sets N. */
static void build_group(Grp G) {
    int m = G.m, k = G.k;
    N = m * k;
    int rp[MAXN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int ax = x / k, bx = x % k;
        for (int y = 0; y < N; y++) {
            int cy = y / k, ey = y % k;
            MT[x * N + y] = (int)(((long)ax + (long)rp[bx] * cy) % m) * k + (bx + ey) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
    }
}

/* ---------------------------------------------------------- voltage lift state */

static int dest[MAXD][MAXA];   /* dart (k, i) goes from A_i to B_{dest[k][i]} */
static int volt[MAXD][MAXA];   /* voltage of dart (k, i) */
static int src_[MAXD][MAXA];   /* inverse of dest: src_[k][j] = i */
static int adj[MAXV][MAXD];
static int dist_[MAXV], q_[MAXV];

/* A(i,x) = i*N + x, B(j,y) = a*N + j*N + y. */
static void build_adj(void) {
    int aN = a * N;
    for (int k = 0; k < d; k++)
        for (int i = 0; i < a; i++) src_[k][dest[k][i]] = i;
    for (int i = 0; i < a; i++)
        for (int x = 0; x < N; x++) {
            int v = i * N + x;
            for (int k = 0; k < d; k++) {
                int j = dest[k][i];
                int y = MT[x * N + volt[k][i]];
                adj[v][k] = aN + j * N + y;
            }
        }
    for (int j = 0; j < a; j++)
        for (int y = 0; y < N; y++) {
            int v = aN + j * N + y;
            for (int k = 0; k < d; k++) {
                int i = src_[k][j];
                int x = MT[y * N + INV[volt[k][i]]];
                adj[v][k] = i * N + x;
            }
        }
}

static void random_state(void) {
    for (int k = 0; k < d; k++) {
        int perm[MAXA];
        for (int i = 0; i < a; i++) perm[i] = i;
        if (k > 0)
            for (int i = a - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = perm[i];
                perm[i] = perm[j];
                perm[j] = t;
            }
        for (int i = 0; i < a; i++) {
            dest[k][i] = perm[i];
            volt[k][i] = rndint(N);
        }
    }
}

/* Number of parallel darts (same endpoints and voltage) from some A vertex. */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < a; i++)
        for (int k = 0; k < d; k++)
            for (int l = k + 1; l < d; l++)
                if (dest[k][i] == dest[l][i] && volt[k][i] == volt[l][i]) c++;
    return c;
}

static int bfs_unreached(int src) {
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    q_[t++] = src;
    while (h < t) {
        int v = q_[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        for (int k = 0; k < d; k++) {
            int u = adj[v][k];
            if (dist_[u] < 0) { dist_[u] = dv + 1; q_[t++] = u; }
        }
    }
    return V - t;
}

/* Cost = total pairs (representative, vertex) at distance > D; 0 iff valid. */
static long cost(void) {
    int dup = dup_count();
    if (dup) return (long)dup * V + 1;
    build_adj();
    long c = 0;
    for (int i = 0; i < a; i++) c += bfs_unreached(i * N);
    for (int j = 0; j < a; j++) c += bfs_unreached(a * N + j * N);
    return c;
}

/* Simulated annealing from the current random state. Returns 1 if cost 0 reached. */
static int anneal(double deadline) {
    long cur = cost();
    if (cur == 0) return 1;
    const long L = 4000;
    long it = 0;
    for (;;) {
        if ((it & 127) == 0 && now() >= deadline) return 0;
        double phase = (double)(it % L) / (double)L;
        double T = 0.25 + 2.0 * (1.0 - phase);
        it++;
        int kind = 0, k = 0, i = 0, i2 = 0, oldv = 0;
        if (a > 1 && rndint(4) == 0) {
            kind = 1;
            k = 1 + rndint(d - 1);      /* keep dest[0] = identity */
            i = rndint(a);
            i2 = rndint(a);
            if (i == i2) continue;
            int t = dest[k][i];
            dest[k][i] = dest[k][i2];
            dest[k][i2] = t;
        } else {
            kind = 2;
            k = rndint(d);
            i = rndint(a);
            oldv = volt[k][i];
            volt[k][i] = rndint(N);
            if (volt[k][i] == oldv) continue;
        }
        long nc = cost();
        long delta = nc - cur;
        int accept = (delta <= 0) || (T > 0 && rnd01() < exp(-(double)delta / T));
        if (accept) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            if (kind == 1) {
                int t = dest[k][i];
                dest[k][i] = dest[k][i2];
                dest[k][i2] = t;
            } else {
                volt[k][i] = oldv;
            }
        }
    }
}

/* ---------------------------------------------------------- candidates and output */

typedef struct { int a, N; } Cand;
static Cand cands[MAXCAND];
static int ncand;

static int cmp_cand(const void *x, const void *y) {
    const Cand *p = (const Cand *)x, *q = (const Cand *)y;
    int vp = 2 * p->a * p->N, vq = 2 * q->a * q->N;
    if (vp != vq) return vp < vq ? -1 : 1;
    return p->a - q->a;
}

static int bestV = 0, bestM = 0;
static int bestEu[MAXE], bestEv[MAXE];

static void print_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int x = 0; x < d; x++)
        for (int y = 0; y < d; y++) printf("%d %d\n", x, d + y);
}

static void print_edges(void) {
    printf("%d %d\n", bestV, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestEu[e], bestEv[e]);
}

static int xadj[MAXV][MAXD], xdeg[MAXV];
static int dd_[MAXV], qq_[MAXV];

/* Full BFS from every vertex on the stored edge list. */
static int verify_edges(void) {
    for (int v = 0; v < V; v++) xdeg[v] = 0;
    for (int e = 0; e < bestM; e++) {
        int u = bestEu[e], w = bestEv[e];
        if (u < 0 || w < 0 || u >= V || w >= V || u == w) return 0;
        if (xdeg[u] >= d || xdeg[w] >= d) return 0;
        xadj[u][xdeg[u]++] = w;
        xadj[w][xdeg[w]++] = u;
    }
    for (int v = 0; v < V; v++)
        if (xdeg[v] != d) return 0;
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dd_[v] = -1;
        int h = 0, t = 0;
        dd_[s] = 0;
        qq_[t++] = s;
        while (h < t) {
            int v = qq_[h++];
            if (dd_[v] >= D) continue;
            for (int k = 0; k < xdeg[v]; k++) {
                int u = xadj[v][k];
                if (dd_[u] < 0) { dd_[u] = dd_[v] + 1; qq_[t++] = u; }
            }
        }
        if (t != V) return 0;
    }
    return 1;
}

/* ---------------------------------------------------------- main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed budget vstart\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int vstart = atoi(argv[5]);

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) { print_complete(); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.92;

    long moore = moore_bound();
    int Vmax = moore < MAXV ? (int)moore : MAXV;
    Vmax -= Vmax % 2;
    if (vstart < 2 * d) vstart = 2 * d;

    ncand = 0;
    for (int aa = 1; aa <= MAXA; aa++)
        for (int nn = 2; nn < MAXN; nn++) {
            int vv = 2 * aa * nn;
            if (vv < vstart || vv > Vmax) continue;
            if (ncand < MAXCAND) {
                cands[ncand].a = aa;
                cands[ncand].N = nn;
                ncand++;
            }
        }
    qsort(cands, (size_t)ncand, sizeof(Cand), cmp_cand);

    double slice = budget / 80.0;
    if (slice < 0.1) slice = 0.1;
    if (slice > 0.8) slice = 0.8;

    for (int ci = 0; ci < ncand && now() < t_end; ci++) {
        a = cands[ci].a;
        int nn = cands[ci].N;
        V = 2 * a * nn;
        if (V <= bestV) continue;
        enum_groups(nn);
        if (ngroups == 0) continue;
        shuffle_groups();

        double slice_end = now() + slice;
        if (slice_end > t_end) slice_end = t_end;
        double per = slice / 3.0;
        if (per < 0.03) per = 0.03;

        int found = 0;
        for (int gi = 0; gi < ngroups && now() < slice_end && !found; gi++) {
            build_group(groups[gi]);   /* sets N = nn */
            random_state();
            double dl = now() + per;
            if (dl > slice_end) dl = slice_end;
            found = anneal(dl);
        }
        if (found) {
            build_adj();
            int m = 0;
            for (int v = 0; v < a * N; v++)
                for (int k = 0; k < d; k++) {
                    if (m < MAXE) {
                        bestEu[m] = v;
                        bestEv[m] = adj[v][k];
                        m++;
                    }
                }
            bestV = V;
            bestM = m;
        }
    }

    if (bestV > 0 && verify_edges()) print_edges();
    else print_complete();
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
    if best[0] >= moore or d < 2 or D < 2 or d > 8:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Search only orders above the current best; the C side also scans upward from here.
    vstart = int(0.42 * moore) // 2 * 2
    vstart = max(vstart, best[0] + 1)

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vstart],
                         stdin_graph=None, timeout=budget + 5.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
