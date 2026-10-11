"""Bi-Cayley search program (new construction for the weakest parents).

Main idea: a bipartite graph on two copies of a finite group G, with A_g adjacent to B_{g s}
for s in a d-element set S (containing the identity, WLOG). Left multiplication by G is an
automorphism, so the diameter test needs only two BFS runs, from A_e and B_e. The C engine
anneals S over randomly chosen semidirect groups Z_m x|_r Z_k of growing order and reports the
largest valid order it finds. Python keeps the best algebraic start (K_{d,d}, PG(2,d-1) incidence,
Araujo-Pardo-Lopez, or W(q) incidence) as a fallback and accepts the C result only if lib.is_valid
confirms it.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley diameter search.
 * Usage:  prog d D seed time_limit Nlo
 * Graph:  vertices A_g = g, B_g = N + g for g in group G of order N.
 *         Edge A_g -- B_{g*s} for each s in S, |S| = d, 0 in S (WLOG).
 * Search: simulated annealing over S, cost = vertices not reached within D from A_e and B_e.
 * Output: the largest valid graph found ("n m" then edges), or nothing if none was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXO 512
#define MAXDEG 32
#define MAXG 8192

typedef struct { int m, k, r; } Grp;

static int d, D, N;
static int MT[MAXO][MAXO];
static int IV[MAXO];
static int S[MAXDEG];
static double t_end;
static Grp groups[MAXG];
static int ngroups;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* Build the multiplication and inverse tables of Z_m x|_r Z_k, element a*k+b,
 * (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Returns 0 if some element has no inverse. */
static int set_group(Grp G) {
    int m = G.m, k = G.k, n = m * k;
    if (n > MAXO || n < 1) return 0;
    N = n;
    static int rp[MAXO];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < n; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < n; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < n; x++) {
        IV[x] = -1;
        for (int y = 0; y < n; y++)
            if (MT[x][y] == 0) { IV[x] = y; break; }
        if (IV[x] < 0) return 0;
    }
    return 1;
}

static void enum_groups(int n) {
    ngroups = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (ngroups < MAXG) { groups[ngroups].m = 1; groups[ngroups].k = k; groups[ngroups].r = 0; ngroups++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ngroups < MAXG) { groups[ngroups].m = m; groups[ngroups].k = k; groups[ngroups].r = r; ngroups++; }
        }
    }
}

/* Number of vertices NOT reached from src within distance D. */
static int bfs_unreached(int src) {
    static int dist[2 * MAXO], q[2 * MAXO];
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    q[t++] = src;
    while (h < t) {
        int v = q[h++];
        if (dist[v] >= D) continue;
        int nd = dist[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + MT[v][S[i]];
                if (dist[u] < 0) { dist[u] = nd; q[t++] = u; }
            }
        } else {
            int h0 = v - N;
            for (int i = 0; i < d; i++) {
                int u = MT[h0][IV[S[i]]];
                if (dist[u] < 0) { dist[u] = nd; q[t++] = u; }
            }
        }
    }
    return V - t;
}

/* Anneal S (with S[0] = identity) for the current group. Returns 1 if a valid S is found. */
static int anneal(long iters) {
    static int inS[MAXO];
    memset(inS, 0, sizeof(int) * (size_t)N);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rndint(N); } while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    int cur = bfs_unreached(0) + bfs_unreached(N);
    double T = 1.0;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) return 0;
        int i = 1 + rndint(d - 1);
        int x = rndint(N);
        if (inS[x]) continue;
        int old = S[i];
        S[i] = x;
        inS[old] = 0;
        inS[x] = 1;
        int nc = bfs_unreached(0) + bfs_unreached(N);
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            S[i] = old;
            inS[x] = 0;
            inS[old] = 1;
        }
        T *= 0.9995;
        if (T < 0.15) T = 1.0;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Nlo\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nlo = atoi(argv[5]);
    if (d < 3 || d > MAXDEG || D < 2) return 0;

    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    t_end = now() + limit;

    long mb = moore_bound() / 2;
    int maxN = mb < MAXO - 1 ? (int)mb : MAXO - 1;
    if (Nlo < d) Nlo = d;
    int Nbest = Nlo - 1;
    int have = 0;
    Grp bestG = {1, 1, 0};
    static int bestS[MAXDEG];

    while (now() < t_end) {
        int target = Nbest + 1;
        if (rndint(4) == 0) target++;
        if (target > maxN) {
            target = Nbest + 1;
            if (target > maxN) break;
        }
        if (target < d) target = d;
        enum_groups(target);
        if (ngroups == 0) continue;
        Grp G = groups[rndint(ngroups)];
        if (!set_group(G)) continue;
        if (N < d) continue;
        if (anneal(40000)) {
            Nbest = N;
            bestG = G;
            memcpy(bestS, S, sizeof(S));
            have = 1;
        }
    }

    if (have && set_group(bestG)) {
        for (int i = 0; i < d; i++) S[i] = bestS[i];
        long m = (long)N * d;
        printf("%d %ld\n", 2 * N, m);
        for (int g = 0; g < N; g++)
            for (int i = 0; i < d; i++)
                printf("%d %d\n", g, N + MT[g][S[i]]);
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

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best

    # The C search needs a group order N with 2N > current best order.
    Nlo = best[0] // 2 + 1
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), Nlo],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
