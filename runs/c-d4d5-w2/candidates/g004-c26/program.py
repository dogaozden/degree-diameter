"""Bi-Cayley search for the weakest case. Python builds the best algebraic start (PG(2,q), W(q),
Araujo-Pardo-Lopez, or K_{d,d}) and checks it with lib.is_valid. The C engine then ignores the
start graph and searches for a larger lift of a regular bipartite base over a finite group G.

Construction: vertices A(i,x) and B(j,y) with i, j in 0..p-1 and x, y in G. Each dart (i,j,g) gives
edges A(i,x)-B(j,x*g). Left multiplication is an automorphism, so the diameter test needs BFS only from
the 2p fibre representatives. For p = 1 (Haar-type bi-Cayley graphs) the connection set S with e in S
is enumerated exhaustively; for p = 2 random voltages are hill-climbed. Groups are semidirect products
Z_m x|_r Z_k. Any failure leaves the Python start graph, which is always valid."""
import time
import itertools

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 512
#define MAXV 512
#define MAXDEG 32
#define MAXDART 64
#define MAXE 32768

static int d, D;
static double t_end;
static long moore;

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

static long powmod_l(long b, long e, long m) {
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
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------- group: Z_m x|_r Z_k, element a*k+b, identity 0 ---------- */
static int mulT[MAXG][MAXG];
static int gm, gk, gr;

static int build_group(int N) {
    static int cm[4096], ck[4096], cr[4096];
    int cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 1;
        for (int r = 0; r < rmax; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (cnt < 4096) { cm[cnt] = m; ck[cnt] = k; cr[cnt] = r; cnt++; }
        }
    }
    if (!cnt) return 0;
    int c = rndint(cnt);
    gm = cm[c]; gk = ck[c]; gr = cr[c];
    int rp[MAXG];
    rp[0] = 1 % gm;
    for (int b = 1; b < gk; b++) rp[b] = (int)((long)rp[b - 1] * gr % gm);
    for (int x = 0; x < N; x++) {
        int a = x / gk, b = x % gk;
        for (int y = 0; y < N; y++) {
            int cc = y / gk, e = y % gk;
            mulT[x][y] = (int)(((a + (long)rp[b] * cc) % gm) * gk + (b + e) % gk);
        }
    }
    return 1;
}

/* ---------- base multigraph darts ---------- */
static int p, N, ndart;
static int dA[MAXDART], dB[MAXDART], dG[MAXDART];

/* True if voltage g on dart t does not duplicate another dart with the same (i, j). */
static int volt_free(int t, int g) {
    for (int s = 0; s < ndart; s++)
        if (s != t && dA[s] == dA[t] && dB[s] == dB[t] && dG[s] == g) return 0;
    return 1;
}

/* Random d-regular connected bipartite base on 2 + 2 vertices (p = 2). */
static void random_darts(void) {
    for (;;) {
        ndart = 0;
        int nid = 0, nsw = 0;
        for (int t = 0; t < d; t++) {
            int sw = rndint(2);
            if (sw) nsw++; else nid++;
            for (int i = 0; i < 2; i++) {
                dA[ndart] = i;
                dB[ndart] = sw ? 1 - i : i;
                int g;
                do { g = rndint(N); } while (!volt_free(ndart, g));
                dG[ndart] = g;
                ndart++;
            }
        }
        if (nid && nsw) return;
    }
}

/* ---------- lift adjacency and orbit-reduced diameter test ---------- */
static int adjv[MAXV][MAXDEG], degv[MAXV];

static void build_adj(void) {
    int nv = 2 * p * N;
    for (int v = 0; v < nv; v++) degv[v] = 0;
    for (int t = 0; t < ndart; t++)
        for (int x = 0; x < N; x++) {
            int a = dA[t] * N + x;
            int b = (p + dB[t]) * N + mulT[x][dG[t]];
            adjv[a][degv[a]++] = b;
            adjv[b][degv[b]++] = a;
        }
}

/* Left multiplication is an automorphism, so BFS from the element-0 vertex of each fibre suffices.
 * Returns the number of (representative, vertex) pairs at distance > D. Zero iff diameter <= D. */
static int distv[MAXV], qq[MAXV];
static long orbit_bad(void) {
    int nv = 2 * p * N;
    long bad = 0;
    for (int b = 0; b < 2 * p; b++) {
        for (int v = 0; v < nv; v++) distv[v] = -1;
        int src = b * N, head = 0, tail = 0;
        distv[src] = 0;
        qq[tail++] = src;
        while (head < tail) {
            int v = qq[head++];
            if (distv[v] >= D) continue;
            for (int i = 0; i < degv[v]; i++) {
                int u = adjv[v][i];
                if (distv[u] < 0) {
                    distv[u] = distv[v] + 1;
                    qq[tail++] = u;
                }
            }
        }
        bad += nv - tail;
    }
    return bad;
}

static int check_S(void) {
    build_adj();
    return orbit_bad() == 0;
}

/* ---------- best result ---------- */
static int bestV = 0, bestM = 0;
static int bestU[MAXE], bestW[MAXE];

static void record(void) {
    int m = 0;
    for (int t = 0; t < ndart; t++)
        for (int x = 0; x < N; x++) {
            if (m >= MAXE) return;
            bestU[m] = dA[t] * N + x;
            bestW[m] = (p + dB[t]) * N + mulT[x][dG[t]];
            m++;
        }
    bestM = m;
    bestV = 2 * p * N;
}

/* ---------- p = 1: exhaustive (or random for huge spaces) Haar-type sets, e in S ---------- */
static int next_comb(int *c, int k, int hi) {
    int i = k - 1;
    while (i >= 0 && c[i] == hi - (k - 1 - i)) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    return 1;
}

static double binom_d(int n, int k) {
    double r = 1.0;
    for (int i = 1; i <= k; i++) r = r * (n - k + i) / i;
    return r;
}

static int exhaust_p1(double until) {
    p = 1;
    ndart = d;
    for (int t = 0; t < ndart; t++) { dA[t] = 0; dB[t] = 0; }
    dG[0] = 0;
    int k = d - 1;
    if (k == 0) return check_S();
    if (k > N - 1) return 0;
    if (binom_d(N - 1, k) > 2e6) {
        for (long it = 0;; it++) {
            if ((it & 255) == 0 && now() > until) return 0;
            for (int i = 0; i < k; i++) {
                int v, dup;
                do {
                    v = 1 + rndint(N - 1);
                    dup = 0;
                    for (int j = 0; j < i; j++) if (dG[j + 1] == v) dup = 1;
                } while (dup);
                dG[i + 1] = v;
            }
            if (check_S()) return 1;
        }
    }
    int c[MAXDEG];
    for (int i = 0; i < k; i++) c[i] = 1 + i;
    for (long it = 0;; it++) {
        if ((it & 255) == 0 && now() > until) return 0;
        for (int i = 0; i < k; i++) dG[i + 1] = c[i];
        if (check_S()) return 1;
        if (!next_comb(c, k, N - 1)) return 0;
    }
}

/* ---------- p = 2: hill climb on voltages ---------- */
static int hill_p2(int steps, double until) {
    p = 2;
    random_darts();
    build_adj();
    long bad = orbit_bad();
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(ndart);
        int old = dG[t];
        int g;
        do { g = rndint(N); } while (!volt_free(t, g));
        dG[t] = g;
        build_adj();
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < 0.02) {
            bad = nb;
        } else {
            dG[t] = old;
        }
    }
    build_adj();
    return bad == 0;
}

/* ---------- output ---------- */
static void print_best(void) {
    if (bestM <= 0) { printf("0 0\n"); return; }
    printf("%d %d\n", bestV, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestW[i]);
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int minn = atoi(argv[5]);
    double t0 = now();
    t_end = t0 + budget * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    bestV = minn;
    bestM = 0;
    if (d < 3 || d > 31 || D < 2) { printf("0 0\n"); return 0; }
    moore = moore_bound();

    while (now() < t_end) {
        int pp = (rndint(10) < 6) ? 1 : 2;
        long Nmin = bestV / (2 * pp) + 1;
        long Nl = Nmin + rndint(2);
        if (Nl < d) Nl = d;
        if (2L * pp * Nl > moore || 2 * pp * Nl > MAXV || Nl > MAXG) continue;
        N = (int)Nl;
        if (!build_group(N)) continue;
        double until = now() + 2.0;
        if (until > t_end) until = t_end;
        int ok = 0;
        if (pp == 1) {
            ok = exhaust_p1(until);
        } else {
            while (!ok && now() < until) ok = hill_p2(2000, until);
        }
        if (ok) record();
    }
    print_best();
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
            for p_ in L:
                for r_ in L:
                    if p_ < r_:
                        covered.add((p_, r_))

    edges = []
    for j, L in enumerate(lines):
        for p_ in L:
            edges.append((p_, P + j))
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
