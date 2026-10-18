"""Multi-fibre voltage-lift annealing for the d=5, D=7 target.

Bold change: the parent searched only bi-Cayley lifts (one vertex per side per group element).
This version searches lifts with a base of p A-fibres and p B-fibres (p in 1..4) over random
semidirect products Z_m x| Z_k of order N, so each lift has 2pN vertices. Base structure: d random
permutations sigma_s of {0..p-1}, giving one dart (i, sigma_s(i)) per s, so every fibre vertex has
degree d. Voltages on darts sharing the same (i, j) are kept distinct, so the lift is simple.

Why the orbit check is exact: left multiplication by G is an automorphism of every lift, and it is
transitive on each fibre. Therefore diameter <= D holds iff the BFS from the 2p fibre
identities reaches all 2pN vertices within D steps. The C search uses this as its objective (number
of unreached (source, vertex) pairs), and anneals the voltages with a cooling schedule. Each
(p, N, group) draws fresh voltages and permutations. Success moves the incumbent to 2pN vertices and
the window above it advances. Candidates are checked again in Python with lib.is_valid. If the C
run fails or yields nothing bigger, the algebraic start (hexagon H(4) for d=5, D=7) is returned.
"""
import time
import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre voltage-lift annealer.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 12000
#define MAXD 32
#define MAXP 6
#define MAXND (MAXP * MAXD)
#define MAXE (MAXV * MAXD / 2 + 64)
#define MAXDIV 1024
#define WINDOW 40
#define STEPS 14000
#define ATTEMPTS 2
#define GROUPS 3

static int d, D;
static long moore;
static double t_end;

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

/* Incumbent graph as an edge list. */
static int best_n = 0, best_m = 0;
static int BEU[MAXE], BEV[MAXE];

static void read_start(void) {
    int n, m;
    best_n = 0;
    best_m = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0 || m > MAXE) return;
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n) return;
        BEU[e] = u;
        BEV[e] = v;
    }
    best_n = n;
    best_m = m;
}

/* Semidirect product Z_m x| Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static int Gm, Gk, Gr;
static int rp[MAXV];
static int divs[MAXDIV], ndivs;

static void make_divs(int N) {
    ndivs = 0;
    for (int i = 1; (long)i * i <= N; i++) {
        if (N % i) continue;
        if (ndivs < MAXDIV) divs[ndivs++] = i;
        if (i != N / i && ndivs < MAXDIV) divs[ndivs++] = N / i;
    }
}

static int pick_group(int N) {
    make_divs(N);
    if (ndivs == 0) return 0;
    for (int tries = 0; tries < 300; tries++) {
        int m = divs[rndint(ndivs)];
        int k = N / m;
        int r = m > 1 ? 1 + rndint(m - 1) : 0;
        if (m > 1 && gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        Gm = m;
        Gk = k;
        Gr = r;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

static inline int gmul(int x, int y) {
    int k = Gk;
    int a = x / k, b = x - a * k;
    int c = y / k, e = y - c * k;
    int s = (int)(((long)a + (long)rp[b] * c) % Gm);
    int t = b + e;
    if (t >= k) t -= k;
    return s * k + t;
}

/* Lift state: p A-fibres and p B-fibres, nd = p*d darts. Dart t = s*p + i goes
 * from A-fibre i to B-fibre sig_s(i), with voltage dG[t]. */
static int P_, N_, nd;
static int dI[MAXND], dJ[MAXND], dG[MAXND];
static int degv[MAXV];
static int adjv[MAXV][MAXD];
static int seenv[MAXV], distv[MAXV], qv[MAXV];
static int stamp = 0;

/* True if voltage g on dart t clashes with another dart on the same (i, j) pair. */
static int clash(int t, int g) {
    for (int t2 = 0; t2 < nd; t2++)
        if (t2 != t && dG[t2] == g && dI[t2] == dI[t] && dJ[t2] == dJ[t]) return 1;
    return 0;
}

static void setup_base(int p, int N) {
    P_ = p;
    N_ = N;
    nd = p * d;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < p; i++) {
            int t = s * p + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dG[t] = -1;
        }
    }
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(N); } while (clash(t, g));
        dG[t] = g;
    }
}

static void build_adj(void) {
    int p = P_, N = N_, V = 2 * p * N;
    for (int v = 0; v < V; v++) degv[v] = 0;
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], g = dG[t];
        for (int x = 0; x < N; x++) {
            int a = i * N + x;
            int b = (p + j) * N + gmul(x, g);
            adjv[a][degv[a]++] = b;
            adjv[b][degv[b]++] = a;
        }
    }
}

/* Orbit objective: unreached (source, vertex) pairs at distance > D, sources = fibre identities.
 * Zero exactly when the lift is connected with diameter <= D. */
static long eval_bad(void) {
    int p = P_, N = N_, V = 2 * p * N;
    build_adj();
    long bad = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        stamp++;
        int head = 0, tail = 0;
        seenv[src] = stamp;
        distv[src] = 0;
        qv[tail++] = src;
        while (head < tail) {
            int v = qv[head++];
            int dv = distv[v];
            if (dv >= D) continue;
            for (int i = 0; i < degv[v]; i++) {
                int u = adjv[v][i];
                if (seenv[u] != stamp) {
                    seenv[u] = stamp;
                    distv[u] = dv + 1;
                    qv[tail++] = u;
                }
            }
        }
        bad += V - tail;
    }
    return bad;
}

/* Write the current lift to the incumbent (caller guarantees it is larger). */
static void emit(void) {
    int p = P_, N = N_;
    int m = 0;
    for (int t = 0; t < nd; t++) {
        int i = dI[t], j = dJ[t], g = dG[t];
        for (int x = 0; x < N; x++) {
            if (m >= MAXE) return;
            BEU[m] = i * N + x;
            BEV[m] = (p + j) * N + gmul(x, g);
            m++;
        }
    }
    best_n = 2 * p * N;
    best_m = m;
}

/* Simulated annealing on the voltages of the current lift. Returns 1 on success (incumbent set). */
static int climb(long steps, double until) {
    long bad = eval_bad();
    if (bad == 0) { emit(); return 1; }
    const double T0 = 2.0, T1 = 0.2;
    for (long s = 0; s < steps; s++) {
        if ((s & 127) == 0 && now() > until) return 0;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        int t = rndint(nd);
        int nv = rndint(N_);
        if (nv == dG[t] || clash(t, nv)) continue;
        int old = dG[t];
        dG[t] = nv;
        long nb = eval_bad();
        if (nb == 0) { emit(); return 1; }
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dG[t] = old;
        }
    }
    return 0;
}

static int feasible(int p) {
    long lim = moore < MAXV ? moore : MAXV;
    long Nlo = best_n / (2 * p) + 1;
    if (Nlo < d + 2) Nlo = d + 2;
    return Nlo <= lim / (2 * p);
}

static void search(void) {
    long lim = moore < MAXV ? moore : MAXV;
    while (now() < t_end) {
        int p = -1;
        for (int tr = 0; tr < 8 && p < 0; tr++) {
            int c = 1 + rndint(4);
            if (feasible(c)) p = c;
        }
        if (p < 0) return;
        long Nlo = best_n / (2 * p) + 1;
        if (Nlo < d + 2) Nlo = d + 2;
        long Nmax = lim / (2 * p);
        long span = Nmax - Nlo + 1;
        if (span > WINDOW) span = WINDOW;
        double u = rnd01();
        long N = Nlo + (long)(u * u * (double)span);
        if (N > Nmax) N = Nmax;
        int done = 0;
        for (int gi = 0; gi < GROUPS && !done && now() < t_end; gi++) {
            if (!pick_group((int)N)) break;
            for (int at = 0; at < ATTEMPTS && !done && now() < t_end; at++) {
                setup_base(p, (int)N);
                if (climb(STEPS, t_end)) done = 1;
            }
        }
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
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start();
    moore = moore_bound();
    if (d >= 2 && d <= MAXD && D >= 2) search();

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", BEU[e], BEV[e]);
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 4.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
