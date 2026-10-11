"""Bi-Cayley / group-lift search (replaces the parent's voltage hill-climb and grow-by-two stages).

Each candidate is a lift of a p-vertex-per-side base multigraph over a semidirect product
Z_m x|_r Z_k. Left multiplication by the group is an automorphism of every lift, so the lift
is valid iff the radius-D balls around one vertex per fibre cover the whole graph. Each test
therefore costs only 2p BFS runs.

Stage 1 (p = 1): connection sets S of d group elements with the identity in S (WLOG, by
right translation). Sets are enumerated exhaustively when there are few, and sampled
otherwise, over every group of order N, for N from about 0.55 * Moore/2 upward.
Stage 2 (p = 2..4): random base multigraphs with hill-climbed voltages.

Python keeps the largest valid graph among the algebraic starts and the C output.
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

#define MAXV 512
#define MAXDEG 32
#define MAXG 256
#define MAXP 4
#define MAXSTART 100000
#define SAMPLE_LIMIT 15000
#define STEPS 4000

typedef struct { int m, k, r; } GDesc;
typedef struct { int i, j, g; } Dart;
typedef struct {
    int m, k, r, N;
    int rp[MAXG];
    int mul[MAXG][MAXG];
} Grp;

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
    long res = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) res = res * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return res;
}

/* Element (a,b) of Z_m x|_r Z_k is coded a*k+b; (a,b)(c,e) = (a + r^b c, b + e). Identity is 0. */
static void make_group(Grp *G, int m, int k, int r) {
    int N = m * k;
    G->m = m; G->k = k; G->r = r; G->N = N;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            G->mul[x][y] = (int)(((long)a + (long)G->rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

static int list_groups(int N, GDesc *out, int cap) {
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (cnt < cap) { out[cnt].m = 1; out[cnt].k = k; out[cnt].r = 0; cnt++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (cnt < cap) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static int adjv[MAXV][MAXDEG];
static int degv[MAXV];

/* Explicit lift: dart (i,j,g) joins A(i,x) = i*N+x to B(j, x*g) = p*N + j*N + mul(x,g). */
static int build(int p, const Grp *G, const Dart *dt, int nd) {
    int N = G->N, nv = 2 * p * N;
    for (int v = 0; v < nv; v++) degv[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = p * N + dt[t].j * N + G->mul[x][dt[t].g];
            if (degv[a] >= MAXDEG || degv[b] >= MAXDEG) return 0;
            adjv[a][degv[a]++] = b;
            adjv[b][degv[b]++] = a;
        }
    return 1;
}

/* Number of (source, vertex) pairs at distance > D, over one source per fibre. 0 iff valid. */
static long cost_of(int p, int N) {
    int nv = 2 * p * N;
    static int dist[MAXV], q[MAXV];
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s < p ? s * N : p * N + (s - p) * N;
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[src] = 0;
        q[tail++] = src;
        while (head < tail) {
            int v = q[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < degv[v]; i++) {
                int u = adjv[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    q[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static int best_nv = 0;
static int have_sol = 0;
static int sol_p = 0, sol_nd = 0, sol_N = 0;
static GDesc sol_gd;
static Dart sol_dt[MAXP * MAXDEG];

static int start_n = 0, start_m = 0;
static int su_arr[MAXSTART], sv_arr[MAXSTART];

static void record(int p, int N, GDesc gd, const Dart *dt, int nd) {
    sol_p = p;
    sol_N = N;
    sol_gd = gd;
    sol_nd = nd;
    memcpy(sol_dt, dt, sizeof(Dart) * (size_t)nd);
    best_nv = 2 * p * N;
    have_sol = 1;
}

static void print_adj(int nv) {
    long m = 0;
    for (int v = 0; v < nv; v++) m += degv[v];
    printf("%d %ld\n", nv, m / 2);
    for (int v = 0; v < nv; v++)
        for (int i = 0; i < degv[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
}

static void print_solution(void) {
    static Grp G;
    make_group(&G, sol_gd.m, sol_gd.k, sol_gd.r);
    build(sol_p, &G, sol_dt, sol_nd);
    print_adj(2 * sol_p * sol_N);
}

static void print_start(void) {
    printf("%d %d\n", start_n, start_m);
    for (int e = 0; e < start_m; e++) printf("%d %d\n", su_arr[e], sv_arr[e]);
}

static void print_fallback(void) {
    if (start_n > 0) { print_start(); return; }
    if (D >= 2 && d >= 1 && d <= MAXDEG) {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
    } else {
        printf("1 0\n");
    }
}

static int try_set(int N, const Grp *G, GDesc gd, const int *S) {
    Dart dt[MAXDEG];
    for (int t = 0; t < d; t++) { dt[t].i = 0; dt[t].j = 0; dt[t].g = S[t]; }
    if (!build(1, G, dt, d)) return 0;
    if (cost_of(1, N) != 0) return 0;
    if (2 * N > best_nv) {
        record(1, N, gd, dt, d);
        return 1;
    }
    return 0;
}

/* Stage 1: bi-Cayley graphs over one group, connection set S = {0, s_2, ..., s_d}. */
static void try_N1(int N, double until) {
    static GDesc gd[512];
    static Grp G;
    int ng = list_groups(N, gd, 512);
    int r = d - 1, M = N - 1;
    if (r > M) return;
    for (int gi = 0; gi < ng; gi++) {
        if (now() >= until || 2 * N <= best_nv) return;
        make_group(&G, gd[gi].m, gd[gi].k, gd[gi].r);
        double combos = 1.0;
        for (int i = 0; i < r; i++) combos = combos * (M - i) / (i + 1);
        int S[MAXDEG];
        S[0] = 0;
        if (combos <= SAMPLE_LIMIT) {
            int idx[MAXDEG];
            for (int i = 0; i < r; i++) idx[i] = i;
            for (;;) {
                for (int i = 0; i < r; i++) S[i + 1] = idx[i] + 1;
                if (try_set(N, &G, gd[gi], S)) return;
                int i = r - 1;
                while (i >= 0 && idx[i] == M - r + i) i--;
                if (i < 0) break;
                idx[i]++;
                for (int j = i + 1; j < r; j++) idx[j] = idx[j - 1] + 1;
            }
        } else {
            for (long s = 0; s < SAMPLE_LIMIT; s++) {
                for (int i = 0; i < r; i++) {
                    int x, ok;
                    do {
                        x = 1 + rndint(M);
                        ok = 1;
                        for (int j = 0; j < i; j++)
                            if (S[j + 1] == x) { ok = 0; break; }
                    } while (!ok);
                    S[i + 1] = x;
                }
                if (try_set(N, &G, gd[gi], S)) return;
                if ((s & 255) == 0 && now() >= until) return;
            }
        }
    }
}

/* Stage 2: p-fibre base multigraphs (sum of d permutation matrices) with hill-climbed voltages. */
static void stage2(double until) {
    static GDesc gd[512];
    static Grp G;
    Dart dt[MAXP * MAXDEG];
    while (now() < until) {
        int p = 2 + rndint(3);
        int N = best_nv / (2 * p) + 1 + rndint(2);
        if (N < d || N > MAXG || 2 * p * N > MAXV) continue;
        int ng = list_groups(N, gd, 512);
        if (ng == 0) continue;
        GDesc pick = gd[rndint(ng)];
        make_group(&G, pick.m, pick.k, pick.r);
        int C[MAXP][MAXP];
        memset(C, 0, sizeof(C));
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) C[i][perm[i]]++;
        }
        int nd = 0;
        for (int i = 0; i < p; i++)
            for (int j = 0; j < p; j++)
                for (int c = 0; c < C[i][j]; c++) {
                    dt[nd].i = i; dt[nd].j = j; dt[nd].g = 0;
                    nd++;
                }
        for (int t = 0; t < nd; t++) {
            for (;;) {
                int g = rndint(N), clash = 0;
                for (int u = 0; u < t; u++)
                    if (dt[u].i == dt[t].i && dt[u].j == dt[t].j && dt[u].g == g) { clash = 1; break; }
                if (!clash) { dt[t].g = g; break; }
            }
        }
        if (!build(p, &G, dt, nd)) continue;
        long cst = cost_of(p, N);
        for (int step = 0; step < STEPS && cst > 0; step++) {
            if ((step & 63) == 0 && now() >= until) break;
            int t = rndint(nd);
            int old = dt[t].g;
            int g;
            for (;;) {
                g = rndint(N);
                int clash = 0;
                for (int u = 0; u < nd; u++)
                    if (u != t && dt[u].i == dt[t].i && dt[u].j == dt[t].j && dt[u].g == g) { clash = 1; break; }
                if (!clash) break;
            }
            dt[t].g = g;
            build(p, &G, dt, nd);
            long nc = cost_of(p, N);
            if (nc <= cst) cst = nc;
            else dt[t].g = old;
        }
        if (cst == 0 && 2 * p * N > best_nv) record(p, N, pick, dt, nd);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
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

    if (scanf("%d %d", &start_n, &start_m) != 2) { start_n = 0; start_m = 0; }
    if (start_n < 0 || start_n > MAXV || start_m < 0 || start_m > MAXSTART) { start_n = 0; start_m = 0; }
    int ok = 1;
    for (int e = 0; e < start_m && ok; e++) {
        if (scanf("%d %d", &su_arr[e], &sv_arr[e]) != 2) ok = 0;
        else if (su_arr[e] < 0 || sv_arr[e] < 0 || su_arr[e] >= start_n || sv_arr[e] >= start_n) ok = 0;
    }
    if (!ok) { start_n = 0; start_m = 0; }
    best_nv = start_n;

    if (d >= 3 && d <= MAXDEG && D >= 2) {
        long moore = 0, pw = 1;
        for (int i = 0; i < D; i++) {
            moore += pw;
            pw *= (d - 1);
            if (moore > 1000000L) break;
        }
        moore *= 2;
        long mh = moore / 2;
        if (mh > MAXG) mh = MAXG;
        int hi = (int)mh;
        int lo = best_nv / 2 + 1;
        if (lo < d) lo = d;
        int mid = (int)(0.55 * (double)mh);
        if (mid < lo) mid = lo;
        double s1 = t0 + (t_end - t0) * 0.6;
        for (int N = mid; N <= hi && now() < s1; N++)
            if (2 * N > best_nv) try_N1(N, s1);
        for (int N = lo; N < mid && N <= hi && now() < s1; N++)
            if (2 * N > best_nv) try_N1(N, s1);
        if (now() < t_end) stage2(t_end);
    }

    if (have_sol && best_nv > start_n) print_solution();
    else print_fallback();
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
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
