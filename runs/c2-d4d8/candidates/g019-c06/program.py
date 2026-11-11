"""Abelian bi-Cayley lifts with a record-targeted climb (new engine).

Construction: a 2p-fibre bipartite voltage lift over an abelian group Z_a x Z_b of order N
(a | b, ab = N), with a random d-regular base multigraph on p + p vertices (p = 1 or 2).
Each attempt draws a random abelian group of the target order, assigns distinct voltages, and
anneals them against an orbit-reduced diameter count: BFS from the 2p fibre identities only,
since left multiplication is a fibre-transitive automorphism. The C engine climbs from the
start order, and every few attempts aims directly at record + 2 vertices.

Python supplies the algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}). Each C
output is accepted only if it is larger and passes lib.is_valid. On any failure the best valid
graph so far is returned.
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

#define MAXD 32
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define MAXV 8192

static int d, D;
static long MOORE;
static double t_end;

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

/* Abelian group Z_GA x Z_GB, element i*GB + j. */
static int GA = 1, GB = 1;

static int gmul(int x, int g) {
    int i = x / GB, j = x % GB;
    int gi = g / GB, gj = g % GB;
    int ii = i + gi; if (ii >= GA) ii -= GA;
    int jj = j + gj; if (jj >= GB) jj -= GB;
    return ii * GB + jj;
}

/* Uniformly random factorisation N = a * b with a | b (abelian rank <= 2). */
static int pick_group(int N) {
    long count = 0;
    int ba = 0;
    for (int a = 1; a <= N; a++) {
        if (N % a) continue;
        int b = N / a;
        if (b % a) continue;
        count++;
        if (rndint((int)count) == 0) ba = a;
    }
    if (ba == 0) return 0;
    GA = ba;
    GB = N / ba;
    return 1;
}

static int di[MAXDART], dj[MAXDART], dg[MAXDART];

static void make_darts(int p) {
    int nd = 0;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < p; i++) { di[nd] = i; dj[nd] = perm[i]; nd++; }
    }
}

static int clashes(int t, int g, int nd) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 1;
    return 0;
}

static int gdeg[MAXV], gadj[MAXV][MAXD];
static int NV = 0;

/* A-fibre i element x -> i*N + x; B-fibre j element x -> (p+j)*N + x. */
static void build(int p, int N, int nd) {
    int S = p * N;
    NV = 2 * S;
    for (int v = 0; v < NV; v++) gdeg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int u = di[t] * N + x;
            int v = S + dj[t] * N + gmul(x, dg[t]);
            gadj[u][gdeg[u]++] = v;
            gadj[v][gdeg[v]++] = u;
        }
}

static int dist_b[MAXV], queue_b[MAXV];

/* Unreached (vertex, source) pairs over the 2p fibre identities, within distance D. */
static long orbit_bad(int p, int N) {
    long total = 0;
    for (int f = 0; f < 2 * p; f++) {
        int src = f * N;
        for (int v = 0; v < NV; v++) dist_b[v] = -1;
        int head = 0, tail = 0;
        dist_b[src] = 0;
        queue_b[tail++] = src;
        while (head < tail) {
            int v = queue_b[head++];
            if (dist_b[v] >= D) continue;
            for (int i = 0; i < gdeg[v]; i++) {
                int u = gadj[v][i];
                if (dist_b[u] < 0) {
                    dist_b[u] = dist_b[v] + 1;
                    queue_b[tail++] = u;
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static long anneal(int p, int N, int nd, int maxit, double until) {
    build(p, N, nd);
    long bad = orbit_bad(p, N);
    double T = 1.0;
    for (int it = 0; it < maxit && bad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int ng = rndint(N);
        if (ng == old || clashes(t, ng, nd)) continue;
        dg[t] = ng;
        build(p, N, nd);
        long nb = orbit_bad(p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dg[t] = old;
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    build(p, N, nd);
    return bad;
}

/* Full structural check of the current lift (simple, degree <= d, diameter <= D). */
static int lift_ok(int p, int N, int nd) {
    build(p, N, nd);
    for (int v = 0; v < NV; v++) {
        if (gdeg[v] > d) return 0;
        for (int i = 0; i < gdeg[v]; i++) {
            int u = gadj[v][i];
            if (u == v) return 0;
            for (int j = 0; j < i; j++)
                if (gadj[v][j] == u) return 0;
        }
    }
    return orbit_bad(p, N) == 0;
}

static int hasbest = 0;
static long bestvert = 0;
static int bp, bN, bGA, bGB, bnd;
static int bdi[MAXDART], bdj[MAXDART], bdg[MAXDART];

static int attempt(int p, int N, double until) {
    int nd = p * d;
    if (N < d) return 0;
    if (2L * p * N <= bestvert) return 0;
    while (now() < until) {
        if (!pick_group(N)) return 0;
        make_darts(p);
        for (int t = 0; t < nd; t++) dg[t] = -1;
        for (int t = 0; t < nd; t++) {
            int g;
            do { g = rndint(N); } while (clashes(t, g, nd));
            dg[t] = g;
        }
        long bad = anneal(p, N, nd, 6000, until);
        if (bad == 0 && lift_ok(p, N, nd)) {
            hasbest = 1;
            bestvert = 2L * p * N;
            bp = p; bN = N; bGA = GA; bGB = GB; bnd = nd;
            for (int t = 0; t < nd; t++) {
                bdi[t] = di[t];
                bdj[t] = dj[t];
                bdg[t] = dg[t];
            }
            return 1;
        }
    }
    return 0;
}

static void search(double until, long goal) {
    long step = 1;
    while (now() < until) {
        long cap = MOORE < MAXV ? MOORE : MAXV;
        if (bestvert + 2 > cap) return;
        int p = rndint(3) == 0 ? 2 : 1;
        long N = 0;
        int use_goal = (goal > bestvert) && rndint(2) == 0;
        if (use_goal) {
            N = (goal + 2L * p - 1) / (2L * p);
            if (2L * p * N > cap) use_goal = 0;
        }
        if (!use_goal) {
            for (;;) {
                long S = bestvert / 2 + step;
                N = (S + p - 1) / p;
                if (N < d) N = d;
                if (2L * p * N <= cap) break;
                if (p == 2) { p = 1; continue; }
                if (step > 1) { step = 1; continue; }
                return;
            }
        }
        if (2L * p * N <= bestvert) continue;
        double left = until - now();
        if (left <= 0) break;
        double sl = left / 8;
        if (sl < 0.5) sl = 0.5;
        if (sl > 3.0) sl = 3.0;
        if (sl > left) sl = left;
        int ok = attempt(p, (int)N, now() + sl);
        if (!use_goal) {
            if (ok) { if (step < 512) step *= 2; }
            else if (step > 1) step /= 2;
        }
    }
}

static void print_best(void) {
    int p = bp, N = bN;
    GA = bGA; GB = bGB;
    int S = p * N;
    long m = (long)bnd * N;
    printf("%d %ld\n", 2 * S, m);
    for (int t = 0; t < bnd; t++)
        for (int x = 0; x < N; x++)
            printf("%d %d\n", bdi[t] * N + x, S + bdj[t] * N + gmul(x, bdg[t]));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [start_n] [goal_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long start = (argc > 5) ? atol(argv[5]) : 0;
    long goal = (argc > 6) ? atol(argv[6]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    MOORE = moore_bound();
    bestvert = start;
    search(t_end, goal);
    if (hasbest) print_best();
    else printf("0 0\n");
    return 0;
}
'''

# Best known orders; the C engine aims at record + 2 to beat them.
RECORDS = {(3, 3): 14, (4, 8): 2184}


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

    if d > 31 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    goal = RECORDS[(d, D)] + 2 if (d, D) in RECORDS else 0
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0], goal],
                         stdin_graph=None, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
