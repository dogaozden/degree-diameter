"""Bi-Cayley (Haar-type) search over abelian groups for the weakest target (d=4, D=7).

Change from the parent: the voltage-lift search over explicit non-metacyclic groups is replaced by a
different family. A Haar-type bi-Cayley graph has vertices a_x and b_y for x, y in an abelian group G
of order N, with a_x adjacent to b_{x+s} for each s in a connection set S of size d. The graph is
vertex-transitive (translations and the swap a_x <-> b_{-x} are automorphisms), so the diameter check
only needs BFS from a_0 during search. G is a random mixed-radix abelian group with up to four
factors. The C engine runs simulated annealing over S, with the excess-distance cost, and climbs N
upward from the start order. Every result is re-checked with all-source BFS in C and with lib.is_valid
in Python. If anything fails, the Python fallback (validated K_{d,d} or algebraic start) is returned.

This is untested against the record of 840. For d=4, D=7 the abelian ball growth is polynomial, so
orders near 842 and above are plausible but not verified here.
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

#define MAXN 1536
#define MAXV (2 * MAXN)
#define MAXD 16
#define MAXR 4
#define WIN 20
#define ATT 6
#define STEPS 4000

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Group tables for the current abelian group of order N: ADD[x*N+y] = x+y, NEG[x] = -x. */
static int ADD[MAXN * MAXN];
static int NEG[MAXN];
static int dist[MAXV], qq[MAXV];

static void build_group(int r, const int *M, int N) {
    int w[MAXR];
    w[0] = 1;
    for (int j = 1; j < r; j++) w[j] = w[j - 1] * M[j - 1];
    for (int x = 0; x < N; x++) {
        int s = 0;
        for (int j = 0; j < r; j++) {
            int a = (x / w[j]) % M[j];
            s += ((M[j] - a) % M[j]) * w[j];
        }
        NEG[x] = s;
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int s = 0;
            for (int j = 0; j < r; j++) {
                int a = (x / w[j]) % M[j];
                int b = (y / w[j]) % M[j];
                s += ((a + b) % M[j]) * w[j];
            }
            ADD[x * N + y] = s;
        }
}

static void random_group(int N, int *M, int *r) {
    int rem = N, cnt = 0;
    while (rem > 1 && cnt < MAXR - 1) {
        int divs[64], nd = 0;
        for (int f = 2; f <= rem && nd < 64; f++)
            if (rem % f == 0) divs[nd++] = f;
        int f = divs[rndint(nd)];
        M[cnt++] = f;
        rem /= f;
    }
    if (rem > 1) M[cnt++] = rem;
    *r = cnt;
}

/* Vertices: a_x = x (0..N-1), b_y = N + y. Edges a_x - b_{x+s} for s in S.
 * Cost = sum over vertices of max(0, dist - D), with unreachable vertices charged 2. */
static long eval_cost(int N, const int *S, int src) {
    int nv = 2 * N;
    int NS[MAXD];
    for (int i = 0; i < d; i++) NS[i] = NEG[S[i]];
    for (int v = 0; v < nv; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[src] = 0;
    qq[tail++] = src;
    while (head < tail) {
        int v = qq[head++];
        int nd = dist[v] + 1;
        if (v < N) {
            const int *row = ADD + (size_t)v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (dist[u] < 0) { dist[u] = nd; qq[tail++] = u; }
            }
        } else {
            const int *row = ADD + (size_t)(v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[NS[i]];
                if (dist[u] < 0) { dist[u] = nd; qq[tail++] = u; }
            }
        }
    }
    long cost = 0;
    for (int v = 0; v < nv; v++) {
        if (dist[v] < 0) cost += 2;
        else if (dist[v] > D) cost += dist[v] - D;
    }
    return cost;
}

static int in_set(const int *S, int k, int x) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

static int sa_try(int N, long steps, int *out) {
    int S[MAXD];
    for (int i = 0; i < d; i++) {
        int x;
        do { x = rndint(N); } while (in_set(S, i, x));
        S[i] = x;
    }
    long cur = eval_cost(N, S, 0);
    long best = cur;
    memcpy(out, S, sizeof(int) * d);
    double T = 1.0;
    for (long s = 0; s < steps && cur > 0; s++) {
        int i = rndint(d);
        int old = S[i], x;
        do { x = rndint(N); } while (in_set(S, d, x));
        S[i] = x;
        long c = eval_cost(N, S, 0);
        long delta = c - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = c;
            if (cur < best) {
                best = cur;
                memcpy(out, S, sizeof(int) * d);
            }
        } else {
            S[i] = old;
        }
        T *= 0.998;
        if (T < 0.3) T = 1.0;
    }
    return best == 0;
}

/* Exact check: BFS from every vertex (the graph is vertex-transitive, but this is cheap). */
static int full_check(int N, const int *S) {
    for (int v = 0; v < 2 * N; v++)
        if (eval_cost(N, S, v) > 0) return 0;
    return 1;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double t0 = now();
    t_end = t0 + limit * 0.93;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) n0 = 0;
    (void)m0;

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    long Nmax = moore_bound() / 2;
    if (Nmax > MAXN) Nmax = MAXN;
    int Nlo = n0 / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;

    int bestN = 0, bestR = 0;
    int bestM[MAXR], bestS[MAXD];

    while (now() < t_end && Nlo <= Nmax) {
        int found = 0;
        for (int N = Nlo; N <= Nlo + WIN && N <= Nmax && now() < t_end && !found; N++) {
            for (int a = 0; a < ATT && now() < t_end && !found; a++) {
                int M[MAXR], r = 0;
                random_group(N, M, &r);
                build_group(r, M, N);
                int S[MAXD];
                if (sa_try(N, STEPS, S) && full_check(N, S)) {
                    found = 1;
                    bestN = N;
                    bestR = r;
                    memcpy(bestM, M, sizeof(int) * r);
                    memcpy(bestS, S, sizeof(int) * d);
                }
            }
        }
        if (found) Nlo = bestN + 1;
    }

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(bestR, bestM, bestN);
    int N = bestN;
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + ADD[x * N + bestS[i]]);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 4.0
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
