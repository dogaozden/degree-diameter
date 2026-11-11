"""Bi-Cayley search engine: a different construction family from the lift-based parent.

Each candidate is a bipartite graph with sides A = {(0,g)} and B = {(1,h)} over a finite group G
of order N, with edges (0,g)-(1,g*s) for s in a connection set S of size d. It has 2N vertices
and is d-regular and bipartite by construction.

Left multiplication by G is an automorphism, so diameter <= D holds iff the BFS from (0,e) and
from (1,e) reaches every vertex within D steps. Each check costs two BFS runs.

Groups are Z_m x|_r Z_k with r^k = 1 mod m and gcd(r,m) = 1. This family includes cyclic groups,
direct products and dihedral-type groups. A simulated-annealing search over S minimises the number
of unreached (source, vertex) pairs. A ratchet raises the target order after each success.

Fallbacks: K_{d,d}, then the best algebraic start (PG(2,d-1), Araujo-Lopez, W(q), H(3)). The C
result is used only if it is larger and passes lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley search. Usage: prog d D seed time_limit need
 * Prints a valid bipartite graph with at least `need` vertices, or "0 0" if none was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1100
#define MAXV (2 * MAXG)
#define MAXDEG 32
#define MAXGL 4096

static int d, D;
static double t_end;
static int N;
static int GT[MAXG * MAXG];
static int INV[MAXG];
static int S[MAXDEG];
static int nb[MAXV][MAXDEG];
static int dist[MAXV], qu[MAXV];

static int out_n = 0, out_m = 0;
static int out_u[MAXG * MAXDEG], out_v[MAXG * MAXDEG];

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

static int gcd(int a, int b) {
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

/* ---------------------------------------------------------------- groups */
typedef struct { int m, k, r; } Grp;
static Grp GL[MAXGL];
static int ngl;

/* All groups Z_m x|_r Z_k of order n with m >= 2 (cyclic Z_n is included as m = n, k = 1). */
static void enum_groups(int n) {
    ngl = 0;
    for (int m = 2; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (ngl < MAXGL) {
                GL[ngl].m = m;
                GL[ngl].k = k;
                GL[ngl].r = r;
                ngl++;
            }
        }
    }
}

/* Element a*k + b, product (a,b)(c,e) = (a + r^b c mod m, b + e mod k). Identity is 0. */
static void set_group(Grp G) {
    int m = G.m, k = G.k;
    N = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G.r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)(((long)a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) { INV[x] = y; break; }
}

/* ---------------------------------------------------------------- bi-Cayley graph */
/* Vertex g is (0,g); vertex N+h is (1,h). Neighbours of (0,g): (1,g s). Of (1,h): (0,h s^-1). */
static void set_col(int i) {
    int s = S[i], si = INV[s];
    for (int g = 0; g < N; g++) {
        nb[g][i] = N + GT[g * N + s];
        nb[N + g][i] = GT[g * N + si];
    }
}

static int reach_from(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int h = 0, t = 0;
    dist[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist[v] >= D) continue;
        for (int i = 0; i < d; i++) {
            int u = nb[v][i];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                qu[t++] = u;
            }
        }
    }
    return t;
}

/* Zero iff diameter <= D. Left translations are automorphisms, so two BFS runs suffice. */
static long cost(void) {
    int V = 2 * N;
    return (long)(V - reach_from(0)) + (long)(V - reach_from(N));
}

static void save_solution(void) {
    out_n = 2 * N;
    out_m = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            out_u[out_m] = g;
            out_v[out_m] = nb[g][i];
            out_m++;
        }
}

static int search_group(long steps) {
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(N), ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
        set_col(i);
    }
    long cur = cost();
    double T = 1.5;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 255) == 0 && now() > t_end) break;
        int i = rndint(d), x = rndint(N), ok = 1;
        for (int j = 0; j < d; j++)
            if (S[j] == x) { ok = 0; break; }
        if (!ok) continue;
        int old = S[i];
        S[i] = x;
        set_col(i);
        long nc = cost();
        if (nc <= cur || rnd01() < exp((double)(cur - nc) / T)) {
            cur = nc;
        } else {
            S[i] = old;
            set_col(i);
        }
        T *= 0.9995;
        if (T < 0.15) T = 1.5;
    }
    if (cur == 0) {
        save_solution();
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit need\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long need = atol(argv[5]);
    double t0 = now();
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }
    long moore = moore_bound();
    long lo = (need + 1) / 2;
    if (lo < d) lo = d;
    long hi = moore / 2;
    if (hi > MAXG) hi = MAXG;
    if (lo > hi) { printf("0 0\n"); return 0; }

    while (now() < t_end && lo <= hi) {
        long span = hi - lo;
        long lim = span < 30 ? span : 30;
        int n = (int)(lo + rndint((int)lim + 1));
        if (n < d) n = d;
        enum_groups(n);
        if (ngl == 0) { lo++; continue; }
        Grp G = GL[rndint(ngl)];
        set_group(G);
        int ok = 0;
        for (int rep = 0; rep < 3 && !ok && now() < t_end; rep++)
            ok = search_group(60000);
        if (ok) lo = N + 1;   /* ratchet: next target is strictly larger */
    }

    if (out_m > 0) {
        printf("%d %d\n", out_n, out_m);
        for (int i = 0; i < out_m; i++) printf("%d %d\n", out_u[i], out_v[i]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0] + 2],
                         stdin_graph=None, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
