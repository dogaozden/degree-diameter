"""Multi-fibre bi-lift search for the d=5, D=7 target.

Construction: a bipartite lift with p A-fibres and p B-fibres over a semidirect group
G = Z_m x| Z_k (order N). The base is a d-regular bipartite multigraph on p+p vertices, built
as d permutation matrices. Dart t = s*p + i joins A-fibre i to B-fibre perm_s(i) with voltage g_t:
A_{i,x} ~ B_{j,x*g_t}. Left multiplication by G is an automorphism, so the diameter condition
reduces to BFS from the 2p fibre representatives (A_i,e and B_j,e). The objective is the total
number of unreached vertices from those sources. Simulated annealing on the voltages, with
restarts from fresh random bases and voltages, searches for objective 0 at orders above the
incumbent. Each success is re-verified by a full all-sources BFS in C. Python verifies again with
lib.is_valid. The algebraic starts (projective plane, Araujo-Lopez, generalized quadrangle,
split Cayley hexagon) remain the fallback, so every case returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre voltage-lift annealer.
 * Usage:  prog d D seed time_limit start_n
 * Output: "V E" then E lines "u v" for the largest valid lift found with order > start_n,
 *         or "0 0" if none was found.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXP 4
#define MAXDART 256
#define MAXINC 64
#define MAXVTX (2 * MAXP * MAXN)
#define MAXGC 65536
#define CHAIN 6000
#define ATTEMPT_SEC 5.0

typedef struct { int m, k, r; } GDesc;

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
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
    long s = 0, pw = 1;
    for (int i = 0; i < D; i++) {
        s += pw;
        pw *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ---------- semidirect group Z_m x| Z_k, element a*k+b ---------- */
static int GM, GK, GR, N;
static int rp[MAXN];
static int MT[MAXN * MAXN];
static int INV[MAXN];
static GDesc gcand[MAXGC];

static int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static void setup_group(int m, int k, int r) {
    GM = m; GK = k; GR = r; N = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int *row = MT + (size_t)x * N;
        for (int y = 0; y < N; y++) row[y] = gmul(x, y);
    }
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[(size_t)x * N + y] == 0) { INV[x] = y; break; }
    }
}

static int enum_groups(int n, GDesc *out) {
    int c = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        if (m == 1) {
            if (c < MAXGC) { out[c].m = 1; out[c].k = k; out[c].r = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (c < MAXGC) { out[c].m = m; out[c].k = k; out[c].r = r; c++; }
        }
    }
    return c;
}

static int pick_group(int n) {
    int c = enum_groups(n, gcand);
    if (c == 0) return 0;
    GDesc g = gcand[rndint(c)];
    for (int tries = 0; tries < 60; tries++) {
        GDesc h = gcand[rndint(c)];
        if (h.m > 1 && h.k > 1 && h.r != 1) { g = h; break; }
    }
    setup_group(g.m, g.k, g.r);
    return 1;
}

/* ---------- lift state ---------- */
static int P, nd;
static int ti[MAXDART], tj[MAXDART], vg[MAXDART];
static int inc[MAXP][MAXINC];

static int queue_b[MAXVTX], dist_b[MAXVTX], seen_b[MAXVTX];
static int stamp_b = 0;

static int findp(int *par, int x) {
    while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; }
    return x;
}

/* Dart t = s*p + i: A-fibre i to B-fibre perm_s(i). Base must be connected. */
static void random_base(int p) {
    P = p;
    nd = p * d;
    for (;;) {
        for (int s = 0; s < d; s++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
            }
            for (int i = 0; i < p; i++) { ti[s * p + i] = i; tj[s * p + i] = perm[i]; }
        }
        int par[2 * MAXP];
        for (int v = 0; v < 2 * p; v++) par[v] = v;
        for (int t = 0; t < nd; t++) {
            int a = findp(par, ti[t]), b = findp(par, p + tj[t]);
            if (a != b) par[a] = b;
        }
        int root = findp(par, 0), ok = 1;
        for (int v = 1; v < 2 * p; v++)
            if (findp(par, v) != root) { ok = 0; break; }
        if (ok) break;
    }
    for (int j = 0; j < p; j++) {
        int c = 0;
        for (int t = 0; t < nd; t++)
            if (tj[t] == j && c < MAXINC) inc[j][c++] = t;
    }
}

/* Does voltage g on dart t clash with another dart u < lim on the same (i,j) pair? */
static int clash(int t, int g, int lim) {
    for (int u = 0; u < lim; u++)
        if (u != t && vg[u] == g && ti[u] == ti[t] && tj[u] == tj[t]) return 1;
    return 0;
}

static void random_voltages(void) {
    for (int t = 0; t < nd; t++) {
        int g;
        do g = rndint(N); while (clash(t, g, t));
        vg[t] = g;
    }
}

/* Unreached vertices from one source (source may be any vertex of the lift). */
static long bfs_from(int src) {
    int V = 2 * P * N, AN = P * N;
    int head = 0, tail = 0;
    stamp_b++;
    seen_b[src] = stamp_b;
    dist_b[src] = 0;
    queue_b[tail++] = src;
    while (head < tail) {
        int v = queue_b[head++];
        int dv = dist_b[v];
        if (dv >= D) continue;
        if (v < AN) {
            int i = v / N, x = v % N;
            for (int s = 0; s < d; s++) {
                int t = s * P + i;
                int u = (P + tj[t]) * N + MT[x * N + vg[t]];
                if (seen_b[u] != stamp_b) {
                    seen_b[u] = stamp_b; dist_b[u] = dv + 1; queue_b[tail++] = u;
                }
            }
        } else {
            int w = v - AN, j = w / N, y = w % N;
            for (int k = 0; k < d; k++) {
                int t = inc[j][k];
                int u = ti[t] * N + MT[y * N + INV[vg[t]]];
                if (seen_b[u] != stamp_b) {
                    seen_b[u] = stamp_b; dist_b[u] = dv + 1; queue_b[tail++] = u;
                }
            }
        }
    }
    return (long)(V - tail);
}

/* Orbit-reduced objective: one BFS per fibre representative. */
static long eval_bad(void) {
    long total = 0;
    for (int f = 0; f < 2 * P; f++) total += bfs_from(f * N);
    return total;
}

/* Full check from every vertex. Returns 0 if the lift has diameter <= D. */
static long full_check(void) {
    int V = 2 * P * N;
    for (int v = 0; v < V; v++)
        if (bfs_from(v) != 0) return 1;
    return 0;
}

/* Annealed voltage search on the current base. Returns 1 on a verified zero. */
static int attempt(int p, double until) {
    while (now() < until) {
        random_base(p);
        random_voltages();
        long bad = eval_bad();
        double T = 2.0;
        const double alpha = pow(0.1, 1.0 / CHAIN);
        for (long s = 0; s < CHAIN && bad > 0; s++) {
            if ((s & 255) == 0 && now() > until) break;
            int t = rndint(nd), old = vg[t], g;
            do g = rndint(N); while (clash(t, g, nd));
            vg[t] = g;
            long nb = eval_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else vg[t] = old;
            T *= alpha;
            if (T < 0.2) T = 0.2;
        }
        if (bad == 0 && full_check() == 0) return 1;
    }
    return 0;
}

static int bti[MAXDART], btj[MAXDART], bvg[MAXDART];

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long cur = atol(argv[5]);
    double t0 = now();
    t_end = t0 + (limit > 3.0 ? limit - 1.0 : 0.8 * limit);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    if (d < 2 || d > MAXINC || D < 2) { printf("0 0\n"); return 0; }

    long mb = moore_bound();
    int found = 0;
    int bp = 0, bNN = 0, bm = 0, bk = 0, br = 0, bnd = 0;

    while (now() < t_end && cur < mb) {
        int r = rndint(100);
        int p = r < 10 ? 1 : r < 50 ? 2 : r < 80 ? 3 : 4;
        long per = 2L * p;
        long Nmin = cur / per + 1;          /* smallest N with per*N > cur */
        double u = rnd01();
        long NL = Nmin + (long)(u * sqrt(u) * 60.0);
        if (NL < d) NL = d;
        if (NL > MAXN || per * NL > mb) NL = Nmin;
        if (NL < d) NL = d;
        if (NL > MAXN || per * NL > mb) continue;
        int NN = (int)NL;
        if (!pick_group(NN)) continue;
        double until = now() + ATTEMPT_SEC;
        if (until > t_end) until = t_end;
        if (attempt(p, until)) {
            cur = per * NN;
            found = 1;
            bp = p; bNN = NN; bm = GM; bk = GK; br = GR; bnd = nd;
            memcpy(bti, ti, sizeof(int) * nd);
            memcpy(btj, tj, sizeof(int) * nd);
            memcpy(bvg, vg, sizeof(int) * nd);
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    setup_group(bm, bk, br);
    printf("%d %ld\n", 2 * bp * bNN, (long)bnd * bNN);
    for (int t = 0; t < bnd; t++)
        for (int x = 0; x < bNN; x++) {
            int u = bti[t] * bNN + x;
            int v = (bp + btj[t]) * bNN + MT[x * bNN + bvg[t]];
            printf("%d %d\n", u, v);
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
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

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
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
            # Points of the line: x, and t*x + y for t in GF(q).
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

    if d < 3 or d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 3.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         stdin_graph=None, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
