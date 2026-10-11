"""Bi-Cayley / voltage-lift search with annealed voltages (bold variant).

Differences from the parent:
- Base multigraph is a d-regular bipartite multigraph on P+P fibres, built from d random
  layers of permutations. Each fibre has exactly d darts, so the lift is d-regular.
- Each lift is over an explicitly enumerated group Z_m x|_r Z_k of order N. Groups of
  every order are enumerated, not sampled from the parent's random pool.
- The group acts by LEFT multiplication, which preserves the edges x ~ x*v. So diameter
  is checked by BFS from the 2P fibre identities only.
- Voltages are annealed (cost = unreached (source, vertex) pairs) at a fixed order, and the
  target order is pushed upward one size at a time.
- Fallback: the best of K_{d,d} and the algebraic starts. Every output is checked in Python.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Voltage lifts over semidirect groups with annealed voltages.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 *
 * Lift layout: fibre f in [0, 2P): A-fibres 0..P-1, B-fibres P..2P-1, each of size N.
 * Vertex (f, x) has id f*N + x. Dart t = (i, j, v) joins A(i,x) to B(j, x*v) for all x
 * (left multiplication by group elements is an automorphism, so one BFS per fibre suffices).
 * Each A-fibre and each B-fibre has exactly d darts, so the lift is d-regular.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define MAXPN 128
#define MAXD 16
#define MAXP 3
#define MAXDART (MAXD * MAXP)
#define MAXE 8192

static int d, D, moore;
static double t_end;
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

static int gcd_i(int a, int b) {
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

/* ---------------- group ---------------- */
static int MT[MAXPN][MAXPN];
static int GN;

/* Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static void set_group(int m, int k, int r) {
    int N = m * k;
    GN = N;
    int rp[MAXPN];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

typedef struct { int m, k, r; } Spec;
static Spec specs[4096];
static int nspec;

static void list_groups(int N) {
    nspec = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            specs[nspec].m = 1; specs[nspec].k = k; specs[nspec].r = 0; nspec++;
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            specs[nspec].m = m; specs[nspec].k = k; specs[nspec].r = r; nspec++;
            if (nspec >= 4096) return;
        }
    }
}

/* ---------------- darts ---------------- */
static int P, NN, ND;
static int dI[MAXDART], dJ[MAXDART], dV[MAXDART];
static int sig[MAXD][MAXP];

static int dart_ok(int t) {
    for (int u = 0; u < ND; u++) {
        if (u == t) continue;
        if (dI[u] == dI[t] && dJ[u] == dJ[t] && dV[u] == dV[t]) return 0;
    }
    return 1;
}

static int all_ok(void) {
    for (int t = 0; t < ND; t++) if (!dart_ok(t)) return 0;
    return 1;
}

static int init_state(void) {
    int perm[MAXP];
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < P; i++) sig[L][i] = perm[i];
    }
    for (int t = 0; t < ND; t++) {
        dI[t] = t % P;
        dJ[t] = sig[t / P][t % P];
        dV[t] = rndint(NN);
    }
    for (int r2 = 0; r2 < 300; r2++) {
        for (int t = 0; t < ND; t++)
            if (!dart_ok(t)) dV[t] = rndint(NN);
        if (all_ok()) return 1;
    }
    return 0;
}

/* ---------------- graph ---------------- */
static int adj[MAXN][MAXD];
static int deg[MAXN];
static int NV;

static void build(void) {
    NV = 2 * P * NN;
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int t = 0; t < ND; t++) {
        for (int x = 0; x < NN; x++) {
            int a = dI[t] * NN + x;
            int b = P * NN + dJ[t] * NN + MT[x][dV[t]];
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
    }
}

static int distb[MAXN], qbuf[MAXN];

/* Number of (fibre representative, vertex) pairs at distance > D. Zero iff diameter <= D. */
static long bad_count(void) {
    long total = 0;
    for (int f = 0; f < 2 * P; f++) {
        int src = f * NN;
        for (int v = 0; v < NV; v++) distb[v] = -1;
        int h = 0, tl = 0;
        qbuf[tl++] = src;
        distb[src] = 0;
        while (h < tl) {
            int v = qbuf[h++];
            if (distb[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (distb[u] < 0) {
                    distb[u] = distb[v] + 1;
                    qbuf[tl++] = u;
                }
            }
        }
        total += NV - tl;
    }
    return total;
}

/* ---------------- best ---------------- */
static int bn, bm;
static int be[MAXE][2];

static void record(void) {
    build();
    bn = NV;
    bm = 0;
    for (int u = 0; u < NV; u++)
        for (int i = 0; i < deg[u]; i++)
            if (u < adj[u][i] && bm < MAXE) {
                be[bm][0] = u;
                be[bm][1] = adj[u][i];
                bm++;
            }
}

/* ---------------- annealing ---------------- */
static int anneal(double until, double Tstart) {
    build();
    long cur = bad_count();
    double T = Tstart;
    long it = 0;
    for (;;) {
        if (cur == 0) { build(); return 1; }
        if ((++it & 63) == 0 && now() > until) return 0;
        int t = rndint(ND);
        int old = dV[t];
        int nv = rndint(NN);
        if (nv == old) continue;
        dV[t] = nv;
        if (!dart_ok(t)) { dV[t] = old; continue; }
        build();
        long nb = bad_count();
        if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) {
            cur = nb;
        } else {
            dV[t] = old;
        }
        T *= 0.9995;
        if (T < 0.2) T = Tstart;
    }
}

/* ---------------- main ---------------- */
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
    t_end = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long mb = moore_bound();
    moore = (int)(mb > MAXN ? MAXN : mb);

    bn = 0;
    bm = 0;
    int n, m;
    if (scanf("%d %d", &n, &m) == 2 && n > 0 && n <= MAXN && m >= 0 && m <= MAXE) {
        static int dg[MAXN];
        int ok = 1;
        memset(dg, 0, sizeof(dg));
        for (int e = 0; e < m; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            be[e][0] = u;
            be[e][1] = v;
            dg[u]++;
            dg[v]++;
        }
        if (ok)
            for (int v = 0; v < n; v++)
                if (dg[v] > d) ok = 0;
        if (ok) { bn = n; bm = m; }
    }
    if (bn == 0) {
        bn = 2 * d;
        bm = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) {
                be[bm][0] = a;
                be[bm][1] = d + b;
                bm++;
            }
    }

    while (now() < t_end) {
        int cand[3], nc = 0;
        for (int pp = 1; pp <= 3; pp++) {
            int lo = bn / (2 * pp) + 1;
            if (lo < d) lo = d;
            int hi = moore / (2 * pp);
            if (hi > MAXPN - 1) hi = MAXPN - 1;
            if (lo <= hi) cand[nc++] = pp;
        }
        if (nc == 0) break;
        P = cand[rndint(nc)];
        int lo = bn / (2 * P) + 1;
        if (lo < d) lo = d;
        int hi = moore / (2 * P);
        if (hi > MAXPN - 1) hi = MAXPN - 1;
        int span = hi - lo;
        if (span > 2) span = 2;
        NN = lo + rndint(span + 1);
        ND = d * P;

        list_groups(NN);
        if (nspec == 0) continue;
        Spec s = specs[rndint(nspec)];
        set_group(s.m, s.k, s.r);

        if (!init_state()) continue;
        double until = now() + 1.5;
        if (until > t_end) until = t_end;
        if (anneal(until, 0.8)) {
            int n2 = 2 * P * NN;
            if (n2 > bn) record();
        }
    }

    printf("%d %d\n", bn, bm);
    for (int e = 0; e < bm; e++) printf("%d %d\n", be[e][0], be[e][1]);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = min(0.85 * time_limit, time_limit - 8.0) - (time.monotonic() - t0)
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
