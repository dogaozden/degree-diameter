"""Bold variant: voltage lifts of small cubic bipartite base multigraphs over metacyclic groups.

Parent family: bi-Cayley graphs (one base vertex per side, d darts). This variant:
  * uses P base vertices per side (P = 1..5), with a random d-regular bipartite
    multigraph as the base, and voltages in a group G of order N. The lift has
    2*P*N vertices, degree <= d, and is bipartite by construction;
  * left multiplication by G is an automorphism that is transitive on each fibre,
    so the diameter check needs only BFS from the 2P representatives (A_i,1), (B_j,1);
  * searches by hill-climbing on the cost "number of (representative, vertex) pairs
    at distance > D", with mutations to voltages and to base endpoints;
  * scans total order V = 2*P*N upward from a start value, so the first success
    below the record is kept and larger ones replace it.

If the C search fails, it prints K_{d,d}. Python keeps the larger of the known start
and the C result, and checks every candidate with lib.is_valid.
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
#define MAXD 8
#define MAXP 5
#define MAXK (MAXD * MAXP)
#define MAXGRP 4096
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

static int isab(int gi) { return groups[gi].m == 1 || groups[gi].r == 1; }

/* Element (a, b) is coded a*k + b; identity is 0. */
static int MT[MAXG * MAXG];
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
}

/* ---------------------------------------------------------- lift state */

/* Dart k joins A_{Aend[k]} to B_{Bend[k]} with voltage Volt[k]:
 * A(i,x) ~ B(j, x*g). Each base vertex is incident to exactly d darts. */
static int P, K;
static int Aend[MAXK], Bend[MAXK], Volt[MAXK];

/* Vertex ids: A(i,x) = i*NN + x; B(j,y) = P*NN + j*NN + y. */
static int nbr[MAXV][MAXD];
static int cnt[MAXV];
static int dist_[MAXV], qu[MAXV];

static void build_adj(void) {
    int n = NN, half = P * n, V = 2 * half;
    for (int v = 0; v < V; v++) cnt[v] = 0;
    for (int k = 0; k < K; k++) {
        int ai = Aend[k], bj = Bend[k], g = Volt[k];
        for (int x = 0; x < n; x++) {
            int a = ai * n + x;
            int b = half + bj * n + MT[x * n + g];
            nbr[a][cnt[a]++] = b;
            nbr[b][cnt[b]++] = a;
        }
    }
}

/* Number of vertices within distance D of s. */
static int ball_count(int s, int V) {
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int h = 0, t = 0;
    dist_[s] = 0;
    qu[t++] = s;
    while (h < t) {
        int v = qu[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = nbr[v][i];
            if (dist_[u] < 0) { dist_[u] = dv + 1; qu[t++] = u; }
        }
    }
    return t;
}

/* Zero iff the lift has diameter <= D. Fibres are transitive, so only the
 * representatives A(i,1) and B(j,1) need BFS. */
static long eval_cost(void) {
    build_adj();
    int half = P * NN, V = 2 * half;
    long cost = 0;
    for (int i = 0; i < P; i++) {
        cost += V - ball_count(i * NN, V);
        cost += V - ball_count(half + i * NN, V);
    }
    return cost;
}

static void random_state(int n) {
    for (int k = 0; k < K; k++) {
        Aend[k] = k / d;
        Bend[k] = k / d;
        Volt[k] = rndint(n);
    }
    for (int k = K - 1; k > 0; k--) {
        int j = rndint(k + 1);
        int t = Bend[k]; Bend[k] = Bend[j]; Bend[j] = t;
    }
}

/* Multiset of Aend and Bend is preserved, so every base vertex keeps degree d. */
static void mutate(int n) {
    double r = rnd01();
    if (r < 0.5) {
        Volt[rndint(K)] = rndint(n);
    } else if (r < 0.8) {
        int a = rndint(K), b = rndint(K);
        int t = Bend[a]; Bend[a] = Bend[b]; Bend[b] = t;
    } else {
        int a = rndint(K), b = rndint(K);
        int t = Aend[a]; Aend[a] = Aend[b]; Aend[b] = t;
    }
}

/* ---------------------------------------------------------- search */

static int sP, sK;
static Grp sG;
static int sA[MAXK], sB[MAXK], sV[MAXK];

/* Hill-climb for a lift with p base vertices per side over a group of order n. */
static int search_lift(int p, int n, double until) {
    enum_groups(n);
    if (ngroups == 0) return 0;
    P = p;
    K = d * p;
    int ca[MAXK], cb[MAXK], cv[MAXK];
    while (now() < until) {
        int gi;
        do { gi = rndint(ngroups); } while (isab(gi) && rnd01() < 0.6);
        build_group(groups[gi]);
        random_state(n);
        long cost = eval_cost();
        for (int step = 0; step < STEPS && cost > 0; step++) {
            if (now() >= until) break;
            memcpy(ca, Aend, sizeof(int) * (size_t)K);
            memcpy(cb, Bend, sizeof(int) * (size_t)K);
            memcpy(cv, Volt, sizeof(int) * (size_t)K);
            mutate(n);
            long nc = eval_cost();
            if (nc <= cost || rnd01() < 0.02) {
                cost = nc;
            } else {
                memcpy(Aend, ca, sizeof(int) * (size_t)K);
                memcpy(Bend, cb, sizeof(int) * (size_t)K);
                memcpy(Volt, cv, sizeof(int) * (size_t)K);
            }
        }
        if (cost == 0) {
            sP = P;
            sK = K;
            sG = groups[gi];
            memcpy(sA, Aend, sizeof(int) * (size_t)K);
            memcpy(sB, Bend, sizeof(int) * (size_t)K);
            memcpy(sV, Volt, sizeof(int) * (size_t)K);
            return 1;
        }
    }
    return 0;
}

/* ---------------------------------------------------------- output */

static void set_complete(void) {
    printf("%d %d\n", 2 * d, d * d);
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++)
            printf("%d %d\n", a, d + b);
}

static int is_dup(int v, int i) {
    for (int j = 0; j < i; j++)
        if (nbr[v][j] == nbr[v][i]) return 1;
    return 0;
}

/* Re-verify the saved solution, then print it with duplicate edges removed. */
static int print_solution(void) {
    P = sP;
    K = sK;
    build_group(sG);
    memcpy(Aend, sA, sizeof(int) * (size_t)K);
    memcpy(Bend, sB, sizeof(int) * (size_t)K);
    memcpy(Volt, sV, sizeof(int) * (size_t)K);
    if (eval_cost() != 0) return 0;
    int half = P * NN, V = 2 * half;
    long m = 0;
    for (int v = 0; v < half; v++)
        for (int i = 0; i < d; i++)
            if (!is_dup(v, i)) m++;
    printf("%d %ld\n", V, m);
    for (int v = 0; v < half; v++)
        for (int i = 0; i < d; i++)
            if (!is_dup(v, i)) printf("%d %d\n", v, nbr[v][i]);
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

    if (d < 2 || d > MAXD || D < 2) { set_complete(); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.9;

    long moore = moore_bound();
    long vmax = moore;
    if (vmax > MAXV - 4) vmax = MAXV - 4;
    if (vmax > 2 * (MAXG - 1)) vmax = 2 * (MAXG - 1);
    vmax -= vmax % 2;
    int V0 = vstart < 2 * d ? 2 * d : vstart;
    if (V0 % 2) V0++;

    int bestV = 0;
    for (int V = V0; V <= vmax && now() < t_end; V += 2) {
        int half = V / 2;
        int op[MAXP], on[MAXP], no = 0;
        for (int p = 1; p <= MAXP; p++) {
            if (half % p) continue;
            int n = half / p;
            if (n >= 2 && n < MAXG && d * p <= MAXK) {
                op[no] = p;
                on[no] = n;
                no++;
            }
        }
        if (no == 0) continue;
        double slice = (V <= V0 + 60) ? 1.2 : 0.35;
        double per = slice / no;
        int ok = 0;
        for (int o = 0; o < no && !ok; o++) {
            double until = now() + per;
            if (until > t_end) until = t_end;
            if (search_lift(op[o], on[o], until)) ok = 1;
        }
        if (ok) bestV = V;
    }

    if (bestV > 0 && print_solution()) return 0;
    set_complete();
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

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    # Start the order scan near 0.45 of the Moore bound, and above the known start.
    vstart = max(2 * d, best[0] + 2, int(0.45 * moore))
    if vstart % 2:
        vstart += 1

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), vstart],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
