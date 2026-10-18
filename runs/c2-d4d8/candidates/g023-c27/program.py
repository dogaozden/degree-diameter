"""Bi-Cayley search over matrix groups PGL(2,p) and PSL(2,p).

New construction: a bi-Cayley graph on two copies of a group G, with A_g adjacent to B_{gs} for
each s in a connection set S of size d. Such a graph is bipartite and d-regular. Left
multiplication is an automorphism that acts regularly on each side, so the diameter is at most D
iff the two BFS trees from the identities of the sides reach everything within D. The groups are
PGL(2,p) and PSL(2,p) for small odd primes p, which have orders near half the record order, plus a
few cyclic groups as a fallback. Simulated annealing searches over S.

Python builds the best algebraic start (projective plane, Araujo-Pardo-Lopez, W(q), or K_{d,d}).
C is given the start size and returns a larger bi-Cayley graph only if it is found. Python checks
the result with lib.is_valid and keeps the start otherwise.
"""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 3300
#define MAXPP 83521
#define MAXD 32

static uint16_t MT[MAXG][MAXG];
static int INV[MAXG];
static int matidx[MAXPP];
static int NG, E;
static int S[MAXD], SI[MAXD];
static int dist_[2 * MAXG];
static int qu[2 * MAXG];
static int d, D;
static long MOORE;
static double t_end;

typedef struct { int kind, p, N; } Task;   /* kind 0 cyclic, 1 PGL(2,p), 2 PSL(2,p) */
static Task tasks[64];
static int ntasks;

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

static int imod(int a, int p) {
    a %= p;
    return a < 0 ? a + p : a;
}

static int inv_mod(int a, int p) {
    long r = 1, b = imod(a, p), e = p - 2;
    while (e > 0) {
        if (e & 1) r = r * b % p;
        b = b * b % p;
        e >>= 1;
    }
    return (int)r;
}

static int is_square_mod(int a, int p) {
    for (int r = 0; r < p; r++)
        if (r * r % p == a) return 1;
    return 0;
}

static void decode4(int c, int p, int m[4]) {
    int p2 = p * p, p3 = p2 * p;
    m[0] = c / p3;
    m[1] = (c / p2) % p;
    m[2] = (c / p) % p;
    m[3] = c % p;
}

/* Code of the projective class of matrix m0 (normalised so the first nonzero entry is 1), or -1. */
static int norm_code(const int *m0, int p) {
    int v[4], f = 0;
    for (int i = 0; i < 4; i++) {
        v[i] = imod(m0[i], p);
        if (!f && v[i]) f = v[i];
    }
    if (!f) return -1;
    int iv = inv_mod(f, p);
    int c = 0;
    for (int i = 0; i < 4; i++) c = c * p + (v[i] * iv) % p;
    return c;
}

/* Multiplication table of PGL(2,p) (psl = 0) or PSL(2,p) (psl = 1, det a square), p an odd prime. */
static int build_matrix_group(int p, int psl) {
    int P4 = p * p * p * p;
    if (P4 > MAXPP) return 0;
    for (int c = 0; c < P4; c++) matidx[c] = -1;
    static int elem[MAXG];
    int n = 0;
    for (int c = 0; c < P4; c++) {
        int m[4];
        decode4(c, p, m);
        int f = 0;
        for (int i = 0; i < 4; i++)
            if (m[i]) { f = m[i]; break; }
        if (f != 1) continue;
        int det = imod(m[0] * m[3] - m[1] * m[2], p);
        if (det == 0) continue;
        if (psl && !is_square_mod(det, p)) continue;
        if (n >= MAXG) return 0;
        matidx[c] = n;
        elem[n++] = c;
    }
    NG = n;
    E = matidx[p * p * p + 1];
    if (E < 0) return 0;
    for (int x = 0; x < n; x++) {
        int X[4];
        decode4(elem[x], p, X);
        int A[4] = { X[3], -X[1], -X[2], X[0] };
        int ci = norm_code(A, p);
        if (ci < 0 || matidx[ci] < 0) return 0;
        INV[x] = matidx[ci];
        for (int y = 0; y < n; y++) {
            int Y[4];
            decode4(elem[y], p, Y);
            int M[4] = {
                X[0] * Y[0] + X[1] * Y[2],
                X[0] * Y[1] + X[1] * Y[3],
                X[2] * Y[0] + X[3] * Y[2],
                X[2] * Y[1] + X[3] * Y[3]
            };
            int cc = norm_code(M, p);
            if (cc < 0 || matidx[cc] < 0) return 0;
            MT[x][y] = (uint16_t)matidx[cc];
        }
    }
    return 1;
}

static int build_cyclic(int N) {
    if (N > MAXG || N < 1) return 0;
    NG = N;
    E = 0;
    for (int x = 0; x < N; x++) {
        INV[x] = (N - x) % N;
        for (int y = 0; y < N; y++) MT[x][y] = (uint16_t)((x + y) % N);
    }
    return 1;
}

static int build_task(const Task *t) {
    if (t->kind == 0) return build_cyclic(t->N);
    return build_matrix_group(t->p, t->kind == 2) && NG == t->N;
}

/* Vertices of the bi-Cayley graph: A_g = g, B_h = NG + h. A_g ~ B_{g s} for s in S.
 * Returns the number of vertices NOT within distance D of src. */
static int reach_bad(int src) {
    int tot = 2 * NG;
    for (int v = 0; v < tot; v++) dist_[v] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    qu[tail++] = src;
    while (head < tail) {
        int v = qu[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < NG) {
            const uint16_t *row = MT[v];
            for (int k = 0; k < d; k++) {
                int w = NG + row[S[k]];
                if (dist_[w] < 0) { dist_[w] = dv + 1; qu[tail++] = w; }
            }
        } else {
            const uint16_t *row = MT[v - NG];
            for (int k = 0; k < d; k++) {
                int w = row[SI[k]];
                if (dist_[w] < 0) { dist_[w] = dv + 1; qu[tail++] = w; }
            }
        }
    }
    return tot - tail;
}

/* Zero iff the diameter is at most D (eccentricities are constant on each side). */
static int cost(void) { return reach_bad(E) + reach_bad(NG + E); }

static int in_S(int g) {
    for (int k = 0; k < d; k++)
        if (S[k] == g) return 1;
    return 0;
}

static int in_prefix(int g, int k) {
    for (int j = 0; j < k; j++)
        if (S[j] == g) return 1;
    return 0;
}

/* Anneal over connection sets for the current group until cost 0 or time runs out.
 * Returns 0 on success (S holds the solution), -1 otherwise. */
static int anneal_task(double until) {
    static int bestS[MAXD];
    while (now() < until) {
        for (int k = 0; k < d; k++) {
            int g;
            do { g = rndint(NG); } while (in_prefix(g, k));
            S[k] = g;
        }
        for (int k = 0; k < d; k++) SI[k] = INV[S[k]];
        int c = cost();
        int c0 = c, bestc = c;
        memcpy(bestS, S, sizeof(int) * d);
        double T0 = 1.0 + 0.05 * c0;
        const long iters = 20000;
        for (long it = 0; it < iters && c > 0; it++) {
            if ((it & 127) == 0 && now() > until) break;
            double frac = (double)it / (double)iters;
            double T = T0 * pow(0.5 / T0, frac);
            int k = rndint(d);
            int old = S[k];
            int g = rndint(NG);
            if (in_S(g)) continue;
            S[k] = g;
            SI[k] = INV[g];
            int nc = cost();
            if (nc <= c || rnd01() < exp((double)(c - nc) / T)) {
                c = nc;
                if (c < bestc) {
                    bestc = c;
                    memcpy(bestS, S, sizeof(int) * d);
                }
            } else {
                S[k] = old;
                SI[k] = INV[old];
            }
        }
        if (bestc == 0) {
            memcpy(S, bestS, sizeof(int) * d);
            for (int k = 0; k < d; k++) SI[k] = INV[S[k]];
            return 0;
        }
    }
    return -1;
}

static int task_before(const Task *a, const Task *b) {
    if ((a->kind == 0) != (b->kind == 0)) return a->kind != 0;
    return a->N > b->N;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n] < graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long best_n = (argc >= 6) ? atol(argv[5]) : 0;
    while (getchar() != EOF) {}

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    MOORE = moore_bound();
    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    ntasks = 0;
    static const int primes[] = {3, 5, 7, 11, 13, 17};
    for (int pi = 0; pi < 6; pi++) {
        int p = primes[pi];
        for (int psl = 0; psl < 2; psl++) {
            long N = psl ? (long)p * (p * p - 1) / 2 : (long)p * (p * p - 1);
            if (N < d + 1 || N > MAXG || 2 * N > MOORE || 2 * N <= best_n) continue;
            if (ntasks >= 60) continue;
            tasks[ntasks].kind = 1 + psl;
            tasks[ntasks].p = p;
            tasks[ntasks].N = (int)N;
            ntasks++;
        }
    }
    long c0 = best_n / 2 + 1;
    for (long N = c0; N <= c0 + 2; N++) {
        if (N < d + 1 || N > MAXG || 2 * N > MOORE || 2 * N <= best_n) continue;
        if (ntasks >= 60) break;
        tasks[ntasks].kind = 0;
        tasks[ntasks].p = 0;
        tasks[ntasks].N = (int)N;
        ntasks++;
    }
    for (int i = 1; i < ntasks; i++) {
        Task x = tasks[i];
        int j = i - 1;
        while (j >= 0 && task_before(&x, &tasks[j])) {
            tasks[j + 1] = tasks[j];
            j--;
        }
        tasks[j + 1] = x;
    }

    long best_v = best_n;
    int have = 0;
    Task bt;
    memset(&bt, 0, sizeof bt);
    static int bestS[MAXD];
    const double slice = 3.0;
    for (;;) {
        int active = 0;
        for (int t = 0; t < ntasks && now() < t_end; t++) {
            Task *T = &tasks[t];
            if (2L * T->N <= best_v) continue;
            active = 1;
            if (!build_task(T) || NG <= d) {
                T->N = 0;
                continue;
            }
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (anneal_task(until) == 0) {
                best_v = 2L * NG;
                have = 1;
                bt = *T;
                bt.N = NG;
                memcpy(bestS, S, sizeof(int) * d);
            }
        }
        if (!active || now() >= t_end) break;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    if (!build_task(&bt)) {
        printf("0 0\n");
        return 0;
    }
    memcpy(S, bestS, sizeof(int) * d);
    for (int k = 0; k < d; k++) SI[k] = INV[S[k]];
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int N = NG;
    printf("%d %ld\n", 2 * N, (long)N * d);
    for (int g = 0; g < N; g++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", g, N + (int)MT[g][S[k]]);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 3)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
