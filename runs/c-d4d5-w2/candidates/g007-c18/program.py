"""Bold variant: bi-Cayley (Haar-type) graphs over a wide family of finite groups.

The engine searches graphs on 2N vertices: A-side x and B-side y, with edges x -- y*s for each
s in a d-element set S of group elements. Left multiplication is an automorphism, so the diameter
check needs only two BFS runs (from an A vertex and from a B vertex). Groups are semidirect
products Z_m x| Z_k times a cyclic factor Z_j, enumerated for each order N. Simulated annealing
over S minimises the number of pairs at distance > D. If nothing beats the start graph, the
verbatim start (or K_{d,d}) is returned.
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

#define MAXG 512
#define MAXD 32
#define MAXE (MAXG * MAXD)

typedef struct {
    int N;
    int mul[MAXG][MAXG];
    int inv[MAXG];
} Grp;

typedef struct { int m, k, r, j; } Desc;

static int d, D;
static double t_end;
static Grp G;
static int S[MAXD], Si[MAXD];
static int distv[2 * MAXG], qu[2 * MAXG];
static Desc descs[8192];
static int ndesc;
static char *inbuf;

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
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Enumerate Z_m x|_r Z_k x Z_j with m*k*j = N. Element x = ((a*k)+b)*j + c. */
static void enum_desc(int N) {
    ndesc = 0;
    for (int j = 1; j <= N; j++) {
        if (N % j) continue;
        int M = N / j;
        for (int m = 1; m <= M; m++) {
            if (M % m) continue;
            int k = M / m;
            if (m == 1) {
                if (ndesc < 8192) {
                    descs[ndesc].m = 1; descs[ndesc].k = k;
                    descs[ndesc].r = 0; descs[ndesc].j = j;
                    ndesc++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                if (ndesc < 8192) {
                    descs[ndesc].m = m; descs[ndesc].k = k;
                    descs[ndesc].r = r; descs[ndesc].j = j;
                    ndesc++;
                }
            }
        }
    }
}

static void build_grp(Desc ds) {
    int m = ds.m, k = ds.k, r = ds.r, j = ds.j;
    int N = m * k * j;
    G.N = N;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int c = x % j, t = x / j, b = t % k, a = t / k;
        for (int y = 0; y < N; y++) {
            int c2 = y % j, t2 = y / j, b2 = t2 % k, a2 = t2 / k;
            int A = (int)((a + (long)rp[b] * a2) % m);
            int B = (b + b2) % k;
            int C = (c + c2) % j;
            G.mul[x][y] = ((A * k) + B) * j + C;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (G.mul[x][y] == 0) { G.inv[x] = y; break; }
}

/* BFS from A-vertex (side 0) or B-vertex (side 1) of the bi-Cayley graph with set S.
 * Returns the number of vertices NOT reached within distance D. */
static int bfs_bad(int side, int dd) {
    int N = G.N, V = 2 * N;
    for (int v = 0; v < V; v++) distv[v] = -1;
    int h = 0, t = 0;
    int src = side ? N : 0;
    distv[src] = 0;
    qu[t++] = src;
    while (h < t) {
        int v = qu[h++];
        if (distv[v] >= D) continue;
        if (v < N) {
            for (int i = 0; i < dd; i++) {
                int u = N + G.mul[v][S[i]];
                if (distv[u] < 0) { distv[u] = distv[v] + 1; qu[t++] = u; }
            }
        } else {
            int x = v - N;
            for (int i = 0; i < dd; i++) {
                int u = G.mul[x][Si[i]];
                if (distv[u] < 0) { distv[u] = distv[v] + 1; qu[t++] = u; }
            }
        }
    }
    return V - t;
}

static long eval_bad(int dd) {
    return (long)bfs_bad(0, dd) + (long)bfs_bad(1, dd);
}

static int anneal(int dd, long steps, int *out) {
    int N = G.N;
    static int inS[MAXG];
    memset(inS, 0, sizeof(inS));
    for (int i = 0; i < dd; i++) {
        int x;
        do x = rndint(N); while (inS[x]);
        inS[x] = 1;
        S[i] = x;
        Si[i] = G.inv[x];
    }
    long cur = eval_bad(dd);
    double T = 1.0;
    for (long it = 0; it < steps && cur > 0; it++) {
        if ((it & 255) == 0 && now() > t_end) break;
        int i = rndint(dd), old = S[i], x;
        do x = rndint(N); while (inS[x]);
        inS[old] = 0; inS[x] = 1;
        S[i] = x; Si[i] = G.inv[x];
        long nb = eval_bad(dd);
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            inS[x] = 0; inS[old] = 1;
            S[i] = old; Si[i] = G.inv[old];
        }
        T *= 0.9995;
        if (T < 0.1) T = 1.0;
    }
    if (cur == 0) {
        memcpy(out, S, sizeof(int) * (size_t)dd);
        return 1;
    }
    return 0;
}

static void slurp(void) {
    size_t cap = 1 << 16, len = 0;
    char *buf = malloc(cap + 1);
    for (;;) {
        size_t r = fread(buf + len, 1, cap - len, stdin);
        len += r;
        if (r == 0) break;
        if (len == cap) {
            cap *= 2;
            buf = realloc(buf, cap + 1);
        }
    }
    buf[len] = 0;
    inbuf = buf;
}

static int bestE[MAXE][2];

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    slurp();
    long start_n = 0;
    if (sscanf(inbuf, "%ld", &start_n) != 1) start_n = 0;

    long moore = moore_bound();
    long Nmax = moore / 2;
    long Nlo = start_n / 2 + 1;
    if (Nlo < d + 1) Nlo = d + 1;

    int have = 0, bestN = 0, bestM = 0;
    while (now() < t_end && Nlo <= Nmax) {
        long Nl = Nlo + rndint(3);
        if (Nl > Nmax) Nl = Nlo;
        if (Nl > MAXG) break;
        int N = (int)Nl;
        enum_desc(N);
        if (ndesc == 0) { Nlo++; continue; }
        build_grp(descs[rndint(ndesc)]);
        if (G.N <= d) continue;
        int Sout[MAXD];
        if (anneal(d, 20000, Sout)) {
            memcpy(S, Sout, sizeof(int) * (size_t)d);
            int m = 0;
            for (int x = 0; x < N; x++)
                for (int i = 0; i < d; i++) {
                    bestE[m][0] = x;
                    bestE[m][1] = N + G.mul[x][S[i]];
                    m++;
                }
            bestN = N;
            bestM = m;
            have = 1;
            Nlo = N + 1;
            for (int i = 0; i < d; i++) Si[i] = G.inv[S[i]];
        }
    }

    if (have) {
        printf("%d %d\n", 2 * bestN, bestM);
        for (int e = 0; e < bestM; e++) printf("%d %d\n", bestE[e][0], bestE[e][1]);
    } else if (start_n > 0) {
        fputs(inbuf, stdout);
    } else {
        printf("%d %d\n", 2 * d, d * d);
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) printf("%d %d\n", a, d + b);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
