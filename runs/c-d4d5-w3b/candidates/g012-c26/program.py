"""Bi-Cayley lift search for bipartite degree-diameter graphs.

Python builds the best algebraic start (K_{d,d}, PG(2,q) incidence, W(q) incidence, or the
Araujo-Pardo-Lopez graph when it applies) and checks it with lib.is_valid. The C engine then
searches a different family from that start: bi-Cayley (voltage) lifts over finite groups.

Group: Z_m x|_r Z_k, element a*k+b, with (a,b)(c,e) = (a + r^b c mod m, b+e mod k). Cyclic groups
are the r = 1 or m = 1 cases. A lift over G with base of p fibres per side has vertices
(side, fibre, x), and each dart (i, j, g) joins A_{i,x} to B_{j, x*g}.

Phase 1 (p = 1, Haar graphs): for each group order N, ascending, test every connection set
S = {e} + (d-1) elements (exhaustive when small, sampled otherwise). Left multiplication by G is
an automorphism that is transitive on each side, so a BFS from A_e and one from B_e decide the
diameter exactly.

Phase 2 (p = 2..4): random d-regular base multigraphs with random voltages over random groups of
orders just above the current best, tested by the same orbit BFS.

Every candidate that beats the current best passes a full C check (degree, simplicity, bipartite,
all-pairs diameter) before it is recorded. Python validates the final output and keeps the start
graph if the C result is not larger and valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV 4096
#define MAXDEG 32
#define MAXP 4
#define MAXSPEC 512

static int d, D;
static long moore;
static double t_stop;

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

static long moore_bound(int dd, int DD) {
    if (DD <= 0 || dd <= 0) return 1;
    if (dd == 1) return 2;
    if (dd == 2) return 2L * DD;
    long s = 0, p = 1;
    for (int i = 0; i < DD; i++) {
        s += p;
        p *= (dd - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static double binom_d(int n, int k) {
    if (k < 0 || k > n) return 0;
    double r = 1;
    for (int i = 1; i <= k; i++) r = r * (double)(n - k + i) / (double)i;
    return r;
}

/* ---------------- groups ---------------- */
static int G_N;
static int mt[MAXG][MAXG];

typedef struct { int m, k, r; } Spec;
static Spec specs[MAXSPEC];
static int nspec;

static void list_groups(int N) {
    nspec = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (nspec < MAXSPEC) { specs[nspec].m = 1; specs[nspec].k = k; specs[nspec].r = 0; nspec++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            if (nspec < MAXSPEC) { specs[nspec].m = m; specs[nspec].k = k; specs[nspec].r = r; nspec++; }
        }
    }
}

static void build_group(Spec s) {
    int m = s.m, k = s.k, N = m * k;
    long rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = rp[b - 1] * s.r % m;
    G_N = N;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            mt[x][y] = (int)(((a + rp[b] * c) % m) * k + (b + e) % k);
        }
    }
}

/* ---------------- lifts ---------------- */
static int NV;
static int adj[MAXV][MAXDEG];
static int deg[MAXV];
static int zero_i[MAXDEG];

static int build_lift(int p, int N, const int *di, const int *dj, const int *dg, int nd) {
    NV = 2 * p * N;
    if (NV > MAXV) return 0;
    for (int v = 0; v < NV; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = di[t] * N + x;
            int b = (p + dj[t]) * N + mt[x][dg[t]];
            if (deg[a] >= d || deg[b] >= d) return 0;
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
    return 1;
}

static int dist_[MAXV], que_[MAXV];

/* Number of vertices reached from src within distance D. */
static int reach_within(int src) {
    for (int v = 0; v < NV; v++) dist_[v] = -1;
    int h = 0, t = 0;
    dist_[src] = 0;
    que_[t++] = src;
    while (h < t) {
        int v = que_[h++];
        if (dist_[v] >= D) continue;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                que_[t++] = u;
            }
        }
    }
    return t;
}

/* Orbit-reduced test: left multiplication is an automorphism, so sources are the element-0
 * vertex of every fibre. */
static int lift_ok(int p, int N) {
    for (int b = 0; b < 2 * p; b++)
        if (reach_within(b * N) != NV) return 0;
    return 1;
}

static int full_check(int p, int N) {
    int half = p * N;
    if (NV < 2 || NV > MAXV) return 0;
    for (int v = 0; v < NV; v++) {
        if (deg[v] > d) return 0;
        for (int i = 0; i < deg[v]; i++) {
            int u = adj[v][i];
            if (u < 0 || u >= NV || u == v) return 0;
            if ((v < half) == (u < half)) return 0;
            for (int j = 0; j < i; j++)
                if (adj[v][j] == u) return 0;
            int found = 0;
            for (int j = 0; j < deg[u]; j++)
                if (adj[u][j] == v) found = 1;
            if (!found) return 0;
        }
    }
    for (int v = 0; v < NV; v++)
        if (reach_within(v) != NV) return 0;
    return 1;
}

/* ---------------- best graph ---------------- */
static int best_NV;
static int have_best;
static int best_adj[MAXV][MAXDEG];
static int best_deg[MAXV];
static int best_nv;

static void record(int p, int N) {
    if (NV <= best_NV) return;
    if (!full_check(p, N)) return;
    best_NV = NV;
    best_nv = NV;
    have_best = 1;
    for (int v = 0; v < NV; v++) {
        best_deg[v] = deg[v];
        memcpy(best_adj[v], adj[v], sizeof(int) * (size_t)deg[v]);
    }
}

static int try_lift(int p, int N, const int *di, const int *dj, const int *dg, int nd) {
    if (2 * p * N > MAXV) return 0;
    if (!build_lift(p, N, di, dj, dg, nd)) return 0;
    if (!lift_ok(p, N)) return 0;
    record(p, N);
    return 1;
}

static void print_best(void) {
    if (!have_best) { printf("0 0\n"); return; }
    long m = 0;
    for (int v = 0; v < best_nv; v++)
        for (int i = 0; i < best_deg[v]; i++)
            if (v < best_adj[v][i]) m++;
    printf("%d %ld\n", best_nv, m);
    for (int v = 0; v < best_nv; v++)
        for (int i = 0; i < best_deg[v]; i++)
            if (v < best_adj[v][i]) printf("%d %d\n", v, best_adj[v][i]);
}

/* ---------------- phase 1: Haar graphs over groups (p = 1) ---------------- */
static int search_p1_N(int N, double until) {
    int k = d - 1;
    int dg[MAXDEG];
    int comb[MAXDEG];
    list_groups(N);
    if (nspec == 0 || N - 1 < k) return 0;
    long cap = 200000L / nspec;
    if (cap < 2000) cap = 2000;
    for (int s = 0; s < nspec; s++) {
        if (now() > until) return 0;
        build_group(specs[s]);
        if (binom_d(N - 1, k) <= (double)cap) {
            dg[0] = 0;
            for (int i = 0; i < k; i++) comb[i] = i + 1;
            for (;;) {
                for (int i = 0; i < k; i++) dg[i + 1] = comb[i];
                if (try_lift(1, N, zero_i, zero_i, dg, d)) return 1;
                int i = k - 1;
                while (i >= 0 && comb[i] == N - 1 - (k - 1 - i)) i--;
                if (i < 0) break;
                comb[i]++;
                for (int j = i + 1; j < k; j++) comb[j] = comb[j - 1] + 1;
            }
        } else {
            for (long it = 0; it < cap; it++) {
                if ((it & 255) == 0 && now() > until) return 0;
                dg[0] = 0;
                int cnt = 0;
                while (cnt < k) {
                    int x = 1 + rndint(N - 1);
                    int dup = 0;
                    for (int j = 0; j < cnt; j++)
                        if (dg[j + 1] == x) { dup = 1; break; }
                    if (!dup) dg[1 + cnt++] = x;
                }
                if (try_lift(1, N, zero_i, zero_i, dg, d)) return 1;
            }
        }
    }
    return 0;
}

static void phase1(double until) {
    for (int N = 2; N <= MAXG; N++) {
        if (now() > until) break;
        if (2L * N > moore || 2 * N > MAXV) break;
        if (2 * N <= best_NV) continue;
        search_p1_N(N, until);
    }
}

/* ---------------- phase 2: random multi-fibre lifts (p = 2..4) ---------------- */
static void phase2(double until) {
    int perm[MAXP];
    int M[MAXP][MAXP];
    int di[MAXDEG * MAXP], dj[MAXDEG * MAXP], dg[MAXDEG * MAXP];
    while (now() < until) {
        int p = 2 + rndint(3);
        long maxN = moore / (2 * p);
        long capN = MAXV / (2 * p);
        if (capN > MAXG) capN = MAXG;
        if (maxN > capN) maxN = capN;
        long lo = best_NV / (2 * p) + 1;
        if (lo > maxN) continue;
        long span = maxN - lo + 1;
        int N = (int)(lo + rndint((int)(span < 6 ? span : 6)));
        list_groups(N);
        if (nspec == 0) continue;
        build_group(specs[rndint(nspec)]);

        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }

        int nd = 0, ok = 1;
        for (int i = 0; i < p && ok; i++)
            for (int j = 0; j < p && ok; j++) {
                int start = nd;
                for (int c = 0; c < M[i][j]; c++) {
                    if (N <= c) { ok = 0; break; }
                    int g, clash;
                    do {
                        g = rndint(N);
                        clash = 0;
                        for (int q = start; q < nd; q++)
                            if (dg[q] == g) { clash = 1; break; }
                    } while (clash);
                    di[nd] = i; dj[nd] = j; dg[nd] = g;
                    nd++;
                }
            }
        if (!ok) continue;
        try_lift(p, N, di, dj, dg, nd);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit start_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    best_NV = atoi(argv[5]);
    double t0 = now();
    t_stop = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXDEG - 1 || D < 2) { print_best(); return 0; }
    moore = moore_bound(d, D);
    if (best_NV >= moore) { print_best(); return 0; }

    phase1(t0 + (t_stop - t0) * 0.5);
    if (now() < t_stop) phase2(t_stop);
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), best[0]],
                         timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
