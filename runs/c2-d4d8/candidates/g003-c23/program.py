"""Bi-Cayley lift search, v4 (bold change from the voltage/grow engine).

Instead of growing a voltage lift, this version searches bipartite Cayley-type graphs directly.
For a finite group G of order N and a connection set S = {s_1..s_d} of distinct elements, the graph
has vertices a_x and b_y (x, y in G), with a_x adjacent to b_{x s_i}. Left multiplication is an
automorphism, so both sides are vertex-transitive and the diameter test needs only two BFS runs,
one from a_1 and one from b_1. The groups are semidirect products Z_m x| Z_k of order N.

The C engine climbs upward in N. For each target order it anneals the connection set S to zero
out-of-range pairs, then keeps the largest success. Python keeps the best algebraic start as a
fallback, and every returned graph is checked with lib.is_valid."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search over Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit Nmin
 * Output: "n m" then edges of the largest bipartite Cayley graph found (n = 2N), or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXH 4096
#define MAXV (2 * MAXH)
#define MAXD 16
#define MAXCAND 40000
#define STEPS 20000

typedef struct { int m, k, r; } Cand;

static int d, D;
static double t_end;
static Cand cands[MAXCAND];
static int ncand;

static int cm, ck, cN;
static int rpow[MAXH];

static int S[MAXD], Sinv[MAXD];
static int nbA[MAXD][MAXH], nbB[MAXD][MAXH];
static int dist_[MAXV], queue_[MAXV];

static int bestS[MAXD];
static Cand bestC;
static int bestN = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return k <= 1 ? 0 : (int)(rnd() % (uint64_t)k); }
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

/* Enumerate all semidirect groups Z_m x|_r Z_k of order N as candidates. */
static void enum_groups(int N) {
    ncand = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) {
                cands[ncand].m = m;
                cands[ncand].k = k;
                cands[ncand].r = r;
                ncand++;
            }
        }
    }
}

static void set_group(const Cand *c) {
    cm = c->m;
    ck = c->k;
    cN = cm * ck;
    rpow[0] = 1 % cm;
    for (int b = 1; b < ck; b++) rpow[b] = (int)((long)rpow[b - 1] * c->r % cm);
}

/* Element x = a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / ck, b = x % ck, c = y / ck, e = y % ck;
    long t = ((long)a + (long)rpow[b] * c) % cm;
    return (int)(t * ck + (b + e) % ck);
}

/* Inverse of (a,b) is (c,e) with e = -b mod k and c = -a r^{-b} mod m. */
static int ginv(int x) {
    int a = x / ck, b = x % ck;
    int e = (ck - b) % ck;
    long c = (cm - ((long)rpow[e] * a) % cm) % cm;
    return (int)(c * ck + e);
}

static void upd(int i, int N) {
    for (int x = 0; x < N; x++) nbA[i][x] = N + gmul(x, S[i]);
    for (int y = 0; y < N; y++) nbB[i][y] = gmul(y, Sinv[i]);
}

/* BFS up to depth D from src; returns the number of vertices reached. */
static int bfs(int src, int N) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    dist_[src] = 0;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = nbA[i][v];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = nbB[i][y];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Zero iff the graph has diameter <= D (checked from a_1 and b_1 only). */
static long eval_cost(int N) {
    long c = (long)(2 * N - bfs(0, N));
    c += (long)(2 * N - bfs(N, N));
    return c;
}

static int in_S(int g, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == g) return 1;
    return 0;
}

/* Anneal the connection set over group c of order N. On success S holds the solution. */
static int attempt(int N, Cand c) {
    set_group(&c);
    for (int i = 0; i < d; i++) {
        int g;
        do { g = rndint(N); } while (in_S(g, i));
        S[i] = g;
    }
    for (int i = 0; i < d; i++) {
        Sinv[i] = ginv(S[i]);
        upd(i, N);
    }
    long cost = eval_cost(N);
    if (cost == 0) return 1;
    for (long s = 0; s < STEPS; s++) {
        if ((s & 63) == 0 && now() > t_end) return 0;
        int i = rndint(d);
        int g = rndint(N);
        if (in_S(g, d)) continue;
        int old = S[i], oldinv = Sinv[i];
        S[i] = g;
        Sinv[i] = ginv(g);
        upd(i, N);
        long nc = eval_cost(N);
        long delta = nc - cost;
        double T = 1.5 * (1.0 - (double)s / STEPS) + 0.02;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
            if (cost == 0) return 1;
        } else {
            S[i] = old;
            Sinv[i] = oldinv;
            upd(i, N);
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [Nmin]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long Nmin = argc > 5 ? atol(argv[5]) : 1;
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    long moore = 2 * s;
    long Nmax = moore / 2;
    if (Nmax > MAXH) Nmax = MAXH;

    long cur = Nmin - 1;
    if (cur < d - 1) cur = d - 1;
    long J = 0;
    while (now() < t_end && cur + 1 <= Nmax) {
        long target = cur + 1 + rndint((int)(J + 1));
        if (target > Nmax) target = Nmax;
        int N = (int)target;
        enum_groups(N);
        int ok = 0;
        for (int a = 0; a < 3 && !ok && now() < t_end; a++) {
            if (ncand == 0) break;
            Cand c = cands[rndint(ncand)];
            ok = attempt(N, c);
            if (ok) {
                bestC = c;
                memcpy(bestS, S, sizeof(int) * MAXD);
            }
        }
        if (ok) {
            cur = N;
            bestN = N;
            J = 2 * J + 1;
            if (J > cur / 8 + 1) J = cur / 8 + 1;
        } else {
            J = J / 2;
        }
    }

    if (bestN > 0) {
        int N = bestN;
        set_group(&bestC);
        printf("%d %d\n", 2 * N, N * d);
        for (int x = 0; x < N; x++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", x, N + gmul(x, bestS[i]));
    } else {
        printf("0 0\n");
    }
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

    if d > 16 or D < 3 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best
    try:
        n_min = best[0] // 2 + 1
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, n_min],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
