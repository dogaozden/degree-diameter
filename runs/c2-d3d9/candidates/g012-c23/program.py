"""Combined program, v3: exhaustive cyclic bi-Cayley scan, then voltage-lift annealing.

Both parents reached the record 506 for d=3, D=9 with bi-Cayley graphs over Z_253. This version:
  1. Scans cyclic bi-Cayley graphs with S = {0, a, b} exhaustively over N = nlo..Moore/2, using
     a normalisation (scale by units, translate to 0) that makes prime N almost free to check.
     This covers the record N = 253 and everything above it.
  2. Runs simulated annealing over voltage lifts of random d-regular base multigraphs on p+p
     vertices (p = 1..4) over random groups Z_m x| Z_k (including nonabelian ones), targeting
     total order 2pN just above the best found so far.
Diameter is checked exactly: G acts by left multiplication, so one BFS per fibre suffices during
search, and a full BFS from every vertex verifies every result before it is accepted.
Python takes the best known algebraic start (PG(2,q), Araujo-Pardo-Lopez, W(q)) or K_{d,d},
runs the C engine, and checks everything with lib.is_valid, so a valid fallback is always returned.
"""
import itertools
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
#define MAXV 2048
#define MAXDEG 16
#define MAXP 4
#define MAXDARTS (MAXDEG * MAXP)
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

/* ---------------------------------------------------------------- groups */

/* Z_m x|_r Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity = 0. */
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

static void list_groups(int N) {
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

static int MT[MAXG * MAXG];   /* multiplication table of the current group */
static int NG;

static void set_group(Grp G) {
    int n = G.m * G.k;
    static int rp[MAXG];
    NG = n;
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

/* ------------------------------------------------------- lifted graph state */

typedef struct { int i, j, g; } Dart;
static Dart darts[MAXDARTS];
static int nd;          /* number of darts = d * P */
static int P;           /* fibres per side */
static int NN;          /* group order */
static int V;           /* vertex count 2*P*NN */
static int adj[MAXV][MAXDEG];
static int deg[MAXV];

/* A-fibre i, element x -> i*NN + x; B-fibre j, element y -> (P+j)*NN + y.
 * Dart (i, j, g) joins A(i,x) to B(j, x*g). Left multiplication is an automorphism. */
static void build_lift(void) {
    V = 2 * P * NN;
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++) {
            int a = darts[t].i * NN + x;
            int b = (P + darts[t].j) * NN + MT[x * NN + darts[t].g];
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
}

static int dist[MAXV], queue_[MAXV];

/* Sum over fibre representatives f of the number of vertices NOT within distance D of (f, e). */
static long eval_bad(void) {
    long bad = 0;
    for (int f = 0; f < 2 * P; f++) {
        int src = f * NN;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; queue_[tail++] = u; }
            }
        }
        bad += V - tail;
    }
    return bad;
}

/* Exact full verification: simple, bipartite, degree <= d, every pair within D. */
static int verify_full(void) {
    int half = P * NN;
    for (int v = 0; v < V; v++) {
        if (deg[v] < 1 || deg[v] > d) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u < 0 || u >= V || u == v) return 0;
            if ((v < half) == (u < half)) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        queue_[tail++] = s;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; queue_[tail++] = u; }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ best graph */

static int bestV = 0;
static int bestDeg[MAXV];
static int bestAdj[MAXV][MAXDEG];

static void save_best(void) {
    bestV = V;
    for (int v = 0; v < V; v++) {
        bestDeg[v] = deg[v];
        for (int i = 0; i < deg[v]; i++) bestAdj[v][i] = adj[v][i];
    }
}

static void set_complete(void) {
    bestV = 2 * d;
    for (int v = 0; v < bestV; v++) bestDeg[v] = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            bestAdj[a][bestDeg[a]++] = d + b;
            bestAdj[d + b][bestDeg[d + b]++] = a;
        }
}

static void print_best(void) {
    long m = 0;
    for (int v = 0; v < bestV; v++) m += bestDeg[v];
    m /= 2;
    printf("%d %ld\n", bestV, m);
    for (int v = 0; v < bestV; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
}

/* ------------------------------------------------- random base and voltages */

static int base_ok(int M[MAXP][MAXP]) {
    int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, cnt = 1;
    seen[0] = 1;
    stack[top++] = 0;
    while (top) {
        int v = stack[--top];
        for (int u = 0; u < 2 * P; u++) {
            if (seen[u]) continue;
            int linked = (v < P) ? (u >= P && M[v][u - P] > 0) : (u < P && M[u][v - P] > 0);
            if (linked) { seen[u] = 1; cnt++; stack[top++] = u; }
        }
    }
    return cnt == 2 * P;
}

/* Voltage not clashing with another dart on the same (i, j) pair (skip index excluded). */
static int fresh_g(int skip, int i, int j) {
    for (;;) {
        int g = rndint(NN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && darts[t].i == i && darts[t].j == j && darts[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Random connected d-regular bipartite multigraph on P+P vertices, then random distinct voltages. */
static void make_base(void) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < P; i++) perm[i] = i;
            for (int i = P - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < P; i++) M[i][perm[i]]++;
        }
        if (base_ok(M)) break;
    }
    nd = 0;
    for (int i = 0; i < P; i++)
        for (int j = 0; j < P; j++)
            for (int c = 0; c < M[i][j]; c++) {
                int g = fresh_g(-1, i, j);
                darts[nd].i = i;
                darts[nd].j = j;
                darts[nd].g = g;
                nd++;
            }
}

/* Simulated annealing on voltages of a random base. Leaves the lift built and returns 1 on success. */
static int lift_attempt(int p, int N, long steps, double until) {
    P = p;
    NN = N;
    make_base();
    build_lift();
    long bad = eval_bad();
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = darts[t].g;
        darts[t].g = fresh_g(t, darts[t].i, darts[t].j);
        build_lift();
        long nb = eval_bad();
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / 2.0)) bad = nb;
        else darts[t].g = old;
    }
    build_lift();
    if (bad != 0) return 0;
    return verify_full();
}

/* ------------------------------------------- phase 1: exhaustive cyclic, d = 3 */

/* Bi-Cayley graph over Z_N with S = {0, a, b}: one lift with P = 1. */
static int try_cyc_S(int a, int b) {
    darts[0].i = 0; darts[0].j = 0; darts[0].g = 0;
    darts[1].i = 0; darts[1].j = 0; darts[1].g = a;
    darts[2].i = 0; darts[2].j = 0; darts[2].g = b;
    nd = 3;
    build_lift();
    if (eval_bad() != 0) return 0;
    return verify_full();
}

/* Up to translation and unit scaling, every 3-set S with a unit difference is {0,1,x}.
 * Sets with no unit difference are {0,a,b} with a, b, b-a all non-units. */
static void cyclic_phase(int nlo, double until) {
    long moore = moore_bound();
    int nmax = (int)(moore / 2);
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    if (2 * nmax > MAXV) nmax = MAXV / 2;
    for (int N = nlo; N <= nmax && now() < until; N++) {
        Grp G = {N, 1, 1};
        set_group(G);
        P = 1;
        NN = N;
        int found = 0;
        long cnt = 0;
        for (int x = 2; x < N && !found; x++) {
            if ((++cnt & 63) == 0 && now() > until) return;
            if (try_cyc_S(1, x)) found = 1;
        }
        for (int a = 2; a < N && !found; a++) {
            if (gcd(a, N) == 1) continue;
            for (int b = a + 1; b < N && !found; b++) {
                if (gcd(b, N) == 1 || gcd(b - a, N) == 1) continue;
                if ((++cnt & 63) == 0 && now() > until) return;
                if (try_cyc_S(a, b)) found = 1;
            }
        }
        if (found) save_best();
    }
}

/* ------------------------------------------- phase 2: lifts over random groups */

static void lift_phase(double until) {
    long moore = moore_bound();
    while (now() < until) {
        if (bestV >= moore) break;
        int r = rndint(10);
        int p = r < 2 ? 1 : r < 6 ? 2 : r < 9 ? 3 : 4;
        long vmin = bestV + 2;
        if (vmin > moore) break;
        long nmin = (vmin + 2L * p - 1) / (2L * p);
        if (nmin < d) nmin = d;
        long nmax = moore / (2L * p);
        if (nmax > MAXG - 1) nmax = MAXG - 1;
        if (nmax > MAXV / (2 * p)) nmax = MAXV / (2 * p);
        if (nmin > nmax) continue;
        long N = nmin + rndint(3);
        if (N > nmax) N = nmax;
        list_groups((int)N);
        if (ngroups == 0) continue;
        set_group(groups[rndint(ngroups)]);
        if (lift_attempt(p, (int)N, 30000, until) && 2L * p * N > bestV) save_best();
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXDEG) {
        printf("0 0\n");
        return 0;
    }
    if (d >= 2 && D >= 2) {
        long moore = moore_bound();
        double span = t_end - t0;
        if (d == 3) {
            int nlo = (int)(moore / 5);
            if (nlo < d + 1) nlo = d + 1;
            cyclic_phase(nlo, t0 + 0.3 * span);
        }
        lift_phase(t_end);
    }
    if (bestV == 0) set_complete();
    print_best();
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
        q = _largest_prime_power_le(min(d - 1, 9))
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 16 or best[0] >= moore:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass  # keep the valid fallback
    return best
