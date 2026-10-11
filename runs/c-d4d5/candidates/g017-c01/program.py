"""Bi-Cayley search over semidirect groups Z_m x|_r Z_k (new construction for the weak target case).

Each candidate is a bi-Cayley graph: A-vertices x and B-vertices y in a group G of order N, with
A_x adjacent to B_{x*s} for s in a d-element set S. Left multiplication is an automorphism that is
transitive on each side, so the diameter is at most D exactly when BFS from A_e and from B_e reaches
all 2N vertices within D steps. The C engine searches random connection sets for each order N,
growing N while it succeeds. Python keeps the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez,
K_{d,d)) as the fallback and validates every output with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXG 300
#define MAXD 40

typedef struct { int m, k, r; } Grp;

static int d, D;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
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
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int N;
static int MT[MAXG][MAXG];
static int INV[MAXG];

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Identity is 0. */
static void build_group(int m, int k, int r) {
    N = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

static int list_groups(int n, Grp *out) {
    int cnt = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        int rmax = m > 1 ? m : 1;
        for (int r = 0; r < rmax; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt < 512) { out[cnt].m = m; out[cnt].k = k; out[cnt].r = r; cnt++; }
        }
    }
    return cnt;
}

static int S[MAXD];
static int dist[2 * MAXG], qu[2 * MAXG];

/* BFS from src over the bi-Cayley graph; true if all 2N vertices lie within distance D. */
static int reach_all(int src) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + MT[v][S[i]];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = MT[y][INV[S[i]]];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; qu[t++] = u; }
            }
        }
    }
    return t == V;
}

static int check(void) { return reach_all(0) && reach_all(N); }

static void random_S(void) {
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(N), ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
    }
}

static Grp gl[512];
static int BE[MAXG * MAXD][2];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_order\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int ord = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }
    double t_end = now() + limit * 0.92;
    long maxo = moore_bound() / 2;
    if (maxo > MAXG - 1) maxo = MAXG - 1;
    if (ord < d) ord = d;

    int bestO = 0;
    while (ord <= maxo && now() < t_end) {
        int cnt = list_groups(ord, gl);
        int found = 0;
        double deadline = now() + (t_end - now()) * 0.35;
        if (deadline > t_end) deadline = t_end;
        while (!found && cnt > 0 && now() < deadline) {
            for (int g = 0; g < cnt && !found && now() < deadline; g++) {
                build_group(gl[g].m, gl[g].k, gl[g].r);
                for (int t = 0; t < 300 && !found; t++) {
                    random_S();
                    if (check()) {
                        found = 1;
                        int idx = 0;
                        for (int x = 0; x < N; x++)
                            for (int i = 0; i < d; i++) {
                                BE[idx][0] = x;
                                BE[idx][1] = N + MT[x][S[i]];
                                idx++;
                            }
                        bestO = N;
                    }
                }
            }
        }
        if (!found) break;
        ord = ord + 1;
    }

    if (bestO == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * bestO, bestO * d);
    for (int i = 0; i < bestO * d; i++) printf("%d %d\n", BE[i][0], BE[i][1]);
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


def _bicayley(d, D, seed, budget, min_order):
    text = lib.run_c(C_SOURCE, [d, D, seed, budget, min_order],
                     timeout=budget + 5)
    return lib.parse_graph_text(text)


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

    if d > 39 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    min_order = best[0] // 2 + 1  # bi-Cayley graph on 2N vertices must beat best[0]
    try:
        n, e = _bicayley(d, D, seed, budget, min_order)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
