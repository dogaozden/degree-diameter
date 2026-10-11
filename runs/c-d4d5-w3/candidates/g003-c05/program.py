"""Bi-Cayley group search for the bipartite degree-diameter problem.

A bi-Cayley graph over a finite group G of order N has parts A = G and B = G. A vertex g in A
is joined to h in B exactly when g^-1 h lies in a connection set S with |S| = d. Every such
graph is d-regular and bipartite on 2N vertices.

Two facts make the search cheap:
- Left multiplication by x in G maps A-vertices to A-vertices and B-vertices to B-vertices, and
  preserves edges. So the graph has only two vertex orbits, and the diameter is at most D iff
  BFS from A-identity and from B-identity reaches all 2N vertices within D steps.
- Right-multiplying S by any t gives an isomorphic graph, so we can assume the identity is in S.

The C engine searches several group families (cyclic, direct products, dihedral, semidirect
products Z_m x| Z_k) and hill-climbs the connection set. Python keeps the best algebraic start as
a fallback, runs the C search, and accepts its output only if lib.is_valid confirms it.
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

#define MAXN 600
#define MAXD 32
#define MAXCAND 4096

static int d, D;
static double t_end, slice_end;

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

/* ---------- group tables: element 0 is the identity in every family ---------- */
static int N;
static int mt[MAXN][MAXN];
static int invt[MAXN];
static int rp[MAXN];

static void finish_group(void) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x][y] == 0) { invt[x] = y; break; }
}

static void build_cyclic(int n) {
    N = n;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            mt[x][y] = (x + y) % N;
    finish_group();
}

static void build_direct(int a, int b) {
    N = a * b;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            int x1 = x / b, y1 = x % b, x2 = y / b, y2 = y % b;
            mt[x][y] = ((x1 + x2) % a) * b + (y1 + y2) % b;
        }
    finish_group();
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_semi(int m, int k, int r) {
    N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    finish_group();
}

/* Dihedral group of order 2k: element a + k*f, reflection flips the rotation sign. */
static void build_dihedral(int k) {
    N = 2 * k;
    for (int x = 0; x < N; x++) {
        int a = x % k, f = x / k;
        for (int y = 0; y < N; y++) {
            int b = y % k, g = y / k;
            int c = f ? ((a - b) % k + k) % k : (a + b) % k;
            mt[x][y] = ((f + g) & 1) * k + c;
        }
    }
    finish_group();
}

static int cm[MAXCAND], ck[MAXCAND], cr[MAXCAND], ncand;
static void enum_semi(int n) {
    ncand = 0;
    for (int m = 2; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ncand < MAXCAND) { cm[ncand] = m; ck[ncand] = k; cr[ncand] = r; ncand++; }
        }
    }
}

/* ---------- bi-Cayley graph evaluation ---------- */
static int S[MAXD], invS[MAXD];
static int dist_[2 * MAXN], qu[2 * MAXN];

/* Number of vertices reached from src within D steps. */
static int reach_count(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (dist_[v] >= D) continue;
        int nxt = dist_[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + mt[v][S[i]];
                if (dist_[u] < 0) { dist_[u] = nxt; qu[t++] = u; }
            }
        } else {
            int hh = v - N;
            for (int j = 0; j < d; j++) {
                int u = mt[hh][invS[j]];
                if (dist_[u] < 0) { dist_[u] = nxt; qu[t++] = u; }
            }
        }
    }
    return t;
}

/* Count of (source, vertex) pairs at distance > D; zero iff the graph has diameter <= D. */
static int badness(void) {
    for (int j = 0; j < d; j++) invS[j] = invt[S[j]];
    return (2 * N - reach_count(0)) + (2 * N - reach_count(N));
}

/* ---------- best found ---------- */
static int known_n;
static int found;
static int rec_nv, rec_m;
static int rec_u[MAXN * MAXD], rec_v[MAXN * MAXD];

static void record(void) {
    rec_nv = 2 * N;
    rec_m = 0;
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++) {
            rec_u[rec_m] = g;
            rec_v[rec_m] = N + mt[g][S[i]];
            rec_m++;
        }
    found = 1;
    known_n = 2 * N;
}

static int in_S(int x, int upto) {
    for (int j = 0; j < upto; j++)
        if (S[j] == x) return 1;
    return 0;
}

/* One random start followed by annealed single-element replacements in S. */
static int climb(int steps) {
    S[0] = 0; /* identity in S: WLOG by right-translating S */
    for (int i = 1; i < d; i++) {
        int x;
        do { x = 1 + rndint(N - 1); } while (in_S(x, i));
        S[i] = x;
    }
    int cur = badness();
    if (cur == 0) { record(); return 1; }
    double T = 1.0;
    for (int s = 0; s < steps; s++) {
        if ((s & 127) == 0 && now() > slice_end) return 0;
        int i = 1 + rndint(d - 1);
        int x;
        do { x = 1 + rndint(N - 1); } while (in_S(x, d));
        int old = S[i];
        S[i] = x;
        int nb = badness();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
            if (cur == 0) { record(); return 1; }
        } else {
            S[i] = old;
        }
        T *= 0.9995;
        if (T < 0.2) T = 1.0;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [known_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    known_n = argc > 5 ? atoi(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    int nhi = (int)(moore / 2);
    if (nhi > MAXN - 1) nhi = MAXN - 1;
    int fails = 0;

    while (now() < t_end) {
        int nlo = known_n / 2 + 1;   /* need 2N > known_n */
        if (nlo < d + 1) nlo = d + 1;
        if (nlo > nhi) break;
        int span = nhi - nlo + 1;
        int win = 12 + fails / 10;
        if (win > 200) win = 200;
        if (win > span) win = span;
        int n = nlo + rndint(win);

        int fam = rndint(4);
        if (fam == 1 && n % 2 == 0) {
            build_dihedral(n / 2);
        } else if (fam == 2) {
            enum_semi(n);
            if (ncand > 0) {
                int c = rndint(ncand);
                build_semi(cm[c], ck[c], cr[c]);
            } else {
                build_cyclic(n);
            }
        } else if (fam == 3) {
            int cnt = 0, pick = -1;
            for (int a = 2; a <= n / 2; a++)
                if (n % a == 0) { cnt++; if (rndint(cnt) == 0) pick = a; }
            if (pick > 0) build_direct(pick, n / pick);
            else build_cyclic(n);
        } else {
            build_cyclic(n);
        }

        slice_end = now() + 0.3;
        if (slice_end > t_end) slice_end = t_end;
        int ok = 0;
        for (int a = 0; a < 4 && now() < slice_end && !ok; a++)
            ok = climb(2500);
        fails = ok ? 0 : fails + 1;
    }

    if (found) {
        printf("%d %d\n", rec_nv, rec_m);
        for (int e = 0; e < rec_m; e++) printf("%d %d\n", rec_u[e], rec_v[e]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.80 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
