"""Bi-Cayley search for the weak target (d=4, D=7): a different construction family from the parent.

The parent searched voltage lifts with a few base vertices and grew graphs by annealing. This version searches
bi-Cayley graphs instead. For a group G of order N, vertices are A_x and B_x (x in G). A_x is joined to
B_{x s} for each s in a connection set S of d distinct group elements. The graph is bipartite and d-regular.
G acts regularly on each side by left multiplication, so the diameter test needs only two BFS runs, one from
A_e and one from B_e. Groups are semidirect products Z_m x|_r Z_k of every order N in a window just above the
current best half-order. Each candidate S is improved by simulated annealing on the number of pairs at
distance greater than D. Any success is re-checked in C and then in Python with lib.is_valid. If nothing is
found, the Python-side best construction is returned.
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
#define MAXD 16

static int d, D;
static int N;
static int GT[MAXG * MAXG];
static int INV[MAXG];
static int rp[MAXG];
static int S[MAXD];
static int dist_[2 * MAXG];
static int qu[2 * MAXG];

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

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Semidirect product Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b+e). Identity is 0. */
static void build_group(int m, int k, int r) {
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            int A = (int)(((long)a + (long)rp[b] * c) % m);
            GT[x * N + y] = A * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) INV[x] = y;
}

/* Uniformly sample one semidirect group of order n (reservoir sampling over (m, r)). */
static int sample_group(int n, int *om, int *ok, int *orr) {
    long cnt = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { bm = 1; bk = k; br = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    *om = bm;
    *ok = bk;
    *orr = br;
    return 1;
}

/* Number of vertices NOT within distance D of the source (BFS over the bi-Cayley graph). */
static long bfs_bad(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < N) {
            const int *row = GT + v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[t++] = u; }
            }
        } else {
            const int *row = GT + (v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; qu[t++] = u; }
            }
        }
    }
    return V - t;
}

/* Left-regular action on both sides means two BFS runs (from A_e and B_e) decide the diameter. */
static long cost(void) { return bfs_bad(0) + bfs_bad(N); }

static int in_set(int s, int skip, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (j != skip && S[j] == s) return 1;
    return 0;
}

/* Simulated annealing over connection sets S for the current group. Returns the final cost;
 * zero means S is a valid connection set and S holds it. */
static long anneal(long steps, double until) {
    for (int i = 0; i < d; i++) {
        int s;
        do { s = rndint(N); } while (in_set(s, -1, i));
        S[i] = s;
    }
    long cur = cost();
    double T = 1.5;
    for (long it = 0; it < steps && cur > 0; it++) {
        if ((it & 1023) == 0 && now() > until) break;
        int i = rndint(d);
        int old = S[i], s;
        do { s = rndint(N); } while (in_set(s, i, d));
        S[i] = s;
        long c = cost();
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) cur = c;
        else S[i] = old;
        T *= 0.9995;
        if (T < 0.2) T = 1.5;
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit lo < /dev/null\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo = atoi(argv[5]);
    double t0 = now();
    double t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    long Nmax_l = moore / 2;
    if (Nmax_l > 1000) Nmax_l = 1000;
    int Nmax = (int)Nmax_l;

    int target = lo < d + 1 ? d + 1 : lo;
    int fN = 0, fm = 0, fk = 0, fr = 0;
    int fS[MAXD];

    while (now() < t_end) {
        if (target > Nmax) break;
        int N0 = target + rndint(6);
        if (N0 > Nmax) N0 = Nmax;
        if (N0 < d + 1) N0 = d + 1;
        int m, k, r;
        if (!sample_group(N0, &m, &k, &r)) { target++; continue; }
        build_group(m, k, r);
        double until = now() + 2.0;
        if (until > t_end) until = t_end;
        long c = anneal(60000, until);
        if (c == 0) {
            if (N > fN) {
                fN = N;
                fm = m;
                fk = k;
                fr = r;
                memcpy(fS, S, sizeof(int) * d);
            }
            target = N + 1;
        }
    }

    if (fN == 0) {
        printf("0 0\n");
        return 0;
    }
    build_group(fm, fk, fr);
    memcpy(S, fS, sizeof(int) * d);
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %ld\n", 2 * N, (long)d * N);
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, N + GT[x * N + S[i]]);
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

    Returns None if no sign convention yields a graph that passes lib.is_valid.
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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    lo = max(d + 1, best[0] // 2 + 1)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo],
                         stdin_graph=None, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
