"""Bi-Cayley lift search with a Python algebraic fallback.

The C engine searches voltage lifts of small base multigraphs (1 or 2 vertices per side) over
semidirect products Z_m x|_r Z_k. Left multiplication by the group is an automorphism of every
such lift, so the diameter test reduces to BFS from 2p fibre representatives. Simulated
annealing over the voltages looks for a lift with order strictly above the start graph. Python
keeps the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) as a fallback and
validates every returned graph with lib.is_valid.
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

#define MAXV 1024
#define MAXG 1024
#define MAXGL 8192
#define MAXD 16
#define MAXND 64

typedef struct { int m, k, r; } GDesc;

typedef struct {
    int p, N, nd;
    int di[MAXND], dj[MAXND], dg[MAXND];
    int m, k, r;
    int rp[MAXG];
} Lift;

static int d, D, minn;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static int V;
static int adj[MAXV][MAXD];
static int nbr_cnt[MAXV];
static int dist[MAXV], que[MAXV];
static GDesc gl[MAXGL];

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

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
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(Lift *L, int m, int k, int r) {
    L->m = m;
    L->k = k;
    L->r = r;
    L->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) L->rp[b] = (int)((long)L->rp[b - 1] * r % m);
}

static int gmul(const Lift *L, int x, int y) {
    int a = x / L->k, b = x % L->k, c = y / L->k, e = y % L->k;
    return (int)(((long)a + (long)L->rp[b] * c) % L->m) * L->k + (b + e) % L->k;
}

static int list_groups(int N) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < MAXGL) { gl[c].m = 1; gl[c].k = N; gl[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < MAXGL) { gl[c].m = m; gl[c].k = k; gl[c].r = r; c++; }
        }
    }
    return c;
}

static int voltage_ok(const Lift *L, int t, int g) {
    for (int s = 0; s < L->nd; s++)
        if (s != t && L->dg[s] == g && L->di[s] == L->di[t] && L->dj[s] == L->dj[t])
            return 0;
    return 1;
}

/* Lift: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) gives edges A(i,x) - B(j, x*g) for all x. */
static void build_adj(const Lift *L) {
    int p = L->p, N = L->N;
    V = 2 * p * N;
    for (int v = 0; v < V; v++) nbr_cnt[v] = 0;
    for (int t = 0; t < L->nd; t++) {
        for (int x = 0; x < N; x++) {
            int a = L->di[t] * N + x;
            int b = (p + L->dj[t]) * N + gmul(L, x, L->dg[t]);
            if (nbr_cnt[a] < MAXD && nbr_cnt[b] < MAXD) {
                adj[a][nbr_cnt[a]++] = b;
                adj[b][nbr_cnt[b]++] = a;
            }
        }
    }
}

/* Number of (representative, vertex) pairs at distance > D. Zero iff diameter <= D.
 * Left multiplication is an automorphism, so the fibre representatives suffice. */
static long cost_of(const Lift *L) {
    build_adj(L);
    int p = L->p, N = L->N;
    long bad = 0;
    for (int rep = 0; rep < 2 * p; rep++) {
        int src = rep * N;
        for (int v = 0; v < V; v++) dist[v] = -1;
        int h = 0, tl = 0;
        dist[src] = 0;
        que[tl++] = src;
        while (h < tl) {
            int v = que[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < nbr_cnt[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    que[tl++] = u;
                }
            }
        }
        bad += V - tl;
    }
    return bad;
}

static void init_lift(Lift *L, int p, int N, GDesc gd) {
    L->p = p;
    L->N = N;
    L->nd = p * d;
    set_group(L, gd.m, gd.k, gd.r);
    int idx = 0;
    for (int t = 0; t < d; t++) {
        int flip = (p == 2) && rndint(2);
        for (int i = 0; i < p; i++) {
            L->di[idx] = i;
            L->dj[idx] = (p == 2) ? (flip ? 1 - i : i) : 0;
            idx++;
        }
    }
    for (int t = 0; t < L->nd; t++) L->dg[t] = -1;
    for (int t = 0; t < L->nd; t++) {
        int g;
        do { g = rndint(N); } while (!voltage_ok(L, t, g));
        L->dg[t] = g;
    }
}

/* Simulated annealing on the voltages. Returns 1 iff the lift has diameter <= D. */
static int sa_attempt(Lift *L, long steps) {
    long cur = cost_of(L);
    if (cur == 0) return 1;
    for (long it = 0; it < steps; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        double T = 2.0 * (1.0 - (double)it / (double)steps) + 0.05;
        int t = rndint(L->nd);
        int g = rndint(L->N);
        int old = L->dg[t];
        if (g == old || !voltage_ok(L, t, g)) continue;
        L->dg[t] = g;
        long nc = cost_of(L);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            L->dg[t] = old;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_order]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    minn = argc > 5 ? atoi(argv[5]) : 0;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + limit;
    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    int best_n = minn;
    int have_best = 0;
    static Lift best_L;
    static Lift L;

    while (now() < t_end) {
        if ((long)best_n + 2 > moore) break;
        int p = rndint(3) == 0 ? 2 : 1;
        int Nlo = best_n / (2 * p) + 1;
        if (Nlo < d) Nlo = d;
        int N = Nlo + rndint(2);
        if (2L * p * N > moore || 2 * p * N > MAXV || N > MAXG) {
            N = Nlo;
            if (2L * p * N > moore || 2 * p * N > MAXV || N > MAXG) continue;
        }
        int ng = list_groups(N);
        if (ng == 0) continue;
        GDesc gd = gl[rndint(ng)];
        init_lift(&L, p, N, gd);
        if (sa_attempt(&L, 40000)) {
            best_L = L;
            have_best = 1;
            best_n = 2 * p * N;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    build_adj(&best_L);
    long m = 0;
    for (int v = 0; v < V; v++) m += nbr_cnt[v];
    m /= 2;
    printf("%d %ld\n", V, m);
    for (int u = 0; u < V; u++)
        for (int i = 0; i < nbr_cnt[u]; i++)
            if (u < adj[u][i]) printf("%d %d\n", u, adj[u][i]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    try:
        for cand in known_starts(d, D):
            n, e = cand
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
