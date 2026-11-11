"""Bi-Cayley (Haar) hill-climb search, with a new single-source diameter test.

New routine: the Haar graph H(Z_m, S) has vertices a_i, b_j (i, j in Z_m), with a_i ~ b_j iff
j - i in S, |S| = d. The map a_i -> a_{i+t}, b_j -> b_{j+t} is an automorphism, and so is
a_i -> b_{-i}, b_j -> a_{-j}, since a_i ~ b_{i+s} maps to b_{-i} ~ a_{-i-s}. So the graph is
vertex-transitive, and its diameter equals the eccentricity of a_0 alone. Each candidate S is
therefore tested with ONE BFS of O(m d) work, not an all-pairs bitset pass. Translating S
gives an isomorphic graph, so S[0] = 0 is fixed. S is hill-climbed by single-element
replacements, with the number of vertices missed from a_0's D-ball as the objective. The
search walks m upward from the start graph's size and keeps the largest m that succeeds.
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

#define MAXM 2048
#define MAXD 32
#define MAXE 262144
#define MAXNV 4096

static int d, D;
static long moore;
static double t_end;
static int m;
static int S[MAXD];
static int bestS[MAXD];
static int dist_[MAXNV], queue_[MAXNV];
static int sn, sm;
static int eu[MAXE], ev[MAXE];

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
        if (s > 1000000000L) break;
        p *= (d - 1);
        if (p > 1000000000L) p = 1000000000L;
    }
    return 2 * s;
}

static int in_S(int t, int upto) {
    for (int k = 0; k < upto; k++)
        if (S[k] == t) return 1;
    return 0;
}

/* Single-source ball test on the Haar graph H(Z_m, S). Returns the number of
 * vertices NOT within distance D of a_0 (zero means diameter <= D by transitivity). */
static int ball_bad(void) {
    int nv = 2 * m;
    for (int v = 0; v < nv; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[0] = 0;
    queue_[t++] = 0;
    while (h < t) {
        int v = queue_[h++];
        if (dist_[v] >= D) continue;
        int nd = dist_[v] + 1;
        if (v < m) {
            for (int k = 0; k < d; k++) {
                int u = m + (v + S[k]) % m;
                if (dist_[u] < 0) { dist_[u] = nd; queue_[t++] = u; }
            }
        } else {
            int j = v - m;
            for (int k = 0; k < d; k++) {
                int u = (j - S[k] + m) % m;
                if (dist_[u] < 0) { dist_[u] = nd; queue_[t++] = u; }
            }
        }
    }
    return nv - t;
}

/* Hill-climb S (S[0] = 0 fixed) to make every vertex reachable from a_0 within D. */
static int climb(long steps, double until) {
    S[0] = 0;
    for (int k = 1; k < d; k++) {
        int t;
        do { t = rndint(m); } while (in_S(t, k));
        S[k] = t;
    }
    int bad = ball_bad();
    double T = 2.0;
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int k = 1 + rndint(d - 1);
        int old = S[k];
        int t;
        do { t = rndint(m); } while (in_S(t, d));
        S[k] = t;
        int nb = ball_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            S[k] = old;
        }
        T *= 0.9998;
        if (T < 0.2) T = 2.0;
    }
    return bad == 0;
}

static void print_haar(void) {
    printf("%d %d\n", 2 * m, m * d);
    for (int i = 0; i < m; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, m + (i + bestS[k]) % m);
}

static void print_start(void) {
    printf("%d %d\n", sn, sm);
    for (int e = 0; e < sm; e++) printf("%d %d\n", eu[e], ev[e]);
}

static void read_start(void) {
    sn = 0;
    sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; return; }
    if (sn <= 0 || sm < 0 || sm > MAXE) { sn = 0; sm = 0; return; }
    for (int e = 0; e < sm; e++) {
        if (scanf("%d %d", &eu[e], &ev[e]) != 2) { sn = 0; sm = 0; return; }
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
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();
    if (d < 2 || D < 2 || d > MAXD) {
        if (sn > 0) print_start();
        else printf("2 1\n0 1\n");
        return 0;
    }

    moore = moore_bound();
    int have = 0, bestm = 0;
    int mm = sn / 2 + 1;
    if (mm < d + 1) mm = d + 1;
    while (now() < t_end && mm <= MAXM && 2L * mm <= moore) {
        m = mm;
        int ok = 0;
        for (int r = 0; r < 3 && now() < t_end && !ok; r++)
            ok = climb(60000L, t_end);
        if (ok) {
            have = 1;
            bestm = mm;
            memcpy(bestS, S, sizeof(int) * (size_t)d);
        }
        mm++;
    }

    if (have) {
        m = bestm;
        print_haar();
    } else if (sn > 0) {
        print_start();
    } else {
        m = d;
        for (int k = 0; k < d; k++) bestS[k] = k;
        print_haar();
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
