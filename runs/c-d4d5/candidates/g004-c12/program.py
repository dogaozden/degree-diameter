"""Bi-Cayley / voltage-lift simulated annealing for degree-diameter bipartite graphs.

Construction (new in this version): instead of growing the algebraic starts by hill-climbing
lift voltages, the C engine picks a random finite group G of order N (semidirect products
Z_m x|_r Z_k, which includes cyclic and direct products) and a random base of p fibres per side
with d darts per fibre (p <= 4). It anneals the dart voltages with the orbit-reduced objective.
Left multiplication is an automorphism of every such lift, so validity only needs BFS from the
2p fibre representatives, and the graph is never stored during search. Any lift with diameter
<= D and order above the current best is verified in full and kept.

Fallback: the algebraic starts (PG(2,q), Araujo-Pardo-Lopez, W(q), K_{d,d}) are always
checked with lib.is_valid, and the engine's output is only used if it is valid and larger.
Risk: this search does not reproduce the parent's 162-vertex lift, so the d4D5 result depends
on how far the annealing climbs in the budget.
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

#define MAXN 2048
#define MAXD 16
#define MAXG 512
#define MAXP 4
#define MAXT (MAXP * MAXD)
#define MAXE (MAXN * MAXD / 2)

static int d, D;
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
    long s = 0, p = 1;
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000L) break;
    }
    return 2 * s;
}

/* ---------------- groups: Z_m x|_r Z_k, element a*k+b ---------------- */
static int GN;
static int gmt[MAXG][MAXG];
static int ginv[MAXG];

static void make_semidirect(int m, int k, int r) {
    int rp[MAXG];
    GN = m * k;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            gmt[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (gmt[x][y] == 0) ginv[x] = y;
}

/* Uniformly random choice among all (m, k, r) with m*k = N and r^k = 1 mod m. */
static void pick_group(int N) {
    int cm = N, ck = 1, cr = 1;
    long cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            cnt++;
            if (rndint((int)cnt) == 0) { cm = 1; ck = k; cr = 0; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { cm = m; ck = k; cr = r; }
        }
    }
    make_semidirect(cm, ck, cr);
}

/* ---------------- base multigraph: d permutations on p + p fibres ---------------- */
static int P, ND;
static int dfrom[MAXT], dto[MAXT], dg[MAXT];

static int base_connected(int p) {
    int seenA[MAXP] = {0}, seenB[MAXP] = {0};
    seenA[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int t = 0; t < ND; t++) {
            int i = dfrom[t], j = dto[t];
            if (seenA[i] && !seenB[j]) { seenB[j] = 1; changed = 1; }
            if (seenB[j] && !seenA[i]) { seenA[i] = 1; changed = 1; }
        }
    }
    for (int i = 0; i < p; i++)
        if (!seenA[i] || !seenB[i]) return 0;
    return 1;
}

static void make_base(int p) {
    P = p;
    do {
        ND = 0;
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) {
                dfrom[ND] = i;
                dto[ND] = perm[i];
                ND++;
            }
        }
    } while (!base_connected(p));
}

/* Parallel darts (same fibre pair) need distinct voltages, or the lift has multi-edges. */
static int clash(int t, int g) {
    for (int s = 0; s < ND; s++)
        if (s != t && dfrom[s] == dfrom[t] && dto[s] == dto[t] && dg[s] == g) return 1;
    return 0;
}

static void random_voltages(void) {
    for (int t = 0; t < ND; t++) dg[t] = rndint(GN);
    int again = 1;
    while (again) {
        again = 0;
        for (int t = 0; t < ND; t++)
            if (clash(t, dg[t])) { dg[t] = rndint(GN); again = 1; }
    }
}

/* ---------------- orbit-reduced objective ----------------
 * Vertex (fibre f, element x) has id f*GN + x. Edge: A(i,x) -- B(j, x*g) for each dart (i,j,g).
 * Left multiplication is an automorphism, so validity is equivalent to every fibre
 * representative (element 0) reaching all vertices within D steps. */
static int NV;
static int dist_[MAXN], queue_[MAXN];

static long eval_bad(void) {
    long total = 0;
    NV = 2 * P * GN;
    for (int src = 0; src < 2 * P; src++) {
        int s = src * GN;
        for (int v = 0; v < NV; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[s] = 0;
        queue_[tail++] = s;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D) continue;
            int f = v / GN, x = v % GN;
            if (f < P) {
                for (int t = 0; t < ND; t++) {
                    if (dfrom[t] != f) continue;
                    int u = (P + dto[t]) * GN + gmt[x][dg[t]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[tail++] = u; }
                }
            } else {
                int j = f - P;
                for (int t = 0; t < ND; t++) {
                    if (dto[t] != j) continue;
                    int u = dfrom[t] * GN + gmt[x][ginv[dg[t]]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[tail++] = u; }
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

static int build_lift_edges(int *eu, int *ev) {
    int m = 0;
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GN; x++) {
            eu[m] = dfrom[t] * GN + x;
            ev[m] = (P + dto[t]) * GN + gmt[x][dg[t]];
            m++;
        }
    return m;
}

/* ---------------- full independent check ---------------- */
static int nbr[MAXN][MAXD];
static int ndeg[MAXN];
static int colr[MAXN];

static int check_graph(int n, int m, const int *eu, const int *ev) {
    if (n <= 0 || n > MAXN || m < 0 || m > MAXE) return 0;
    if (n > moore_bound()) return 0;
    for (int v = 0; v < n; v++) ndeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (ndeg[u] >= d || ndeg[v] >= d) return 0;
        for (int i = 0; i < ndeg[u]; i++)
            if (nbr[u][i] == v) return 0;
        nbr[u][ndeg[u]++] = v;
        nbr[v][ndeg[v]++] = u;
    }
    for (int v = 0; v < n; v++) colr[v] = -1;
    for (int s = 0; s < n; s++) {
        if (colr[s] >= 0) continue;
        colr[s] = 0;
        int head = 0, tail = 0;
        queue_[tail++] = s;
        while (head < tail) {
            int v = queue_[head++];
            for (int i = 0; i < ndeg[v]; i++) {
                int u = nbr[v][i];
                if (colr[u] < 0) { colr[u] = 1 - colr[v]; queue_[tail++] = u; }
                else if (colr[u] == colr[v]) return 0;
            }
        }
    }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[s] = 0;
        queue_[tail++] = s;
        while (head < tail) {
            int v = queue_[head++];
            if (dist_[v] >= D) continue;
            for (int i = 0; i < ndeg[v]; i++) {
                int u = nbr[v][i];
                if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; queue_[tail++] = u; }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

/* ---------------- best graph ---------------- */
static int best_n = 0, best_m = 0;
static int beu[MAXE], bev[MAXE];
static int teu[MAXE], tev[MAXE];

static void consider(int n, int m, const int *eu, const int *ev) {
    if (n > best_n && check_graph(n, m, eu, ev)) {
        best_n = n;
        best_m = m;
        memcpy(beu, eu, sizeof(int) * (size_t)m);
        memcpy(bev, ev, sizeof(int) * (size_t)m);
    }
}

static void read_start(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return;
    if (n <= 0 || m < 0 || n > MAXN || m > MAXE) return;
    for (int e = 0; e < m; e++)
        if (scanf("%d %d", &teu[e], &tev[e]) != 2) return;
    consider(n, m, teu, tev);
}

/* One annealing run on a random (p, group, base). Returns 1 if a valid lift was found. */
static int try_restart(int p, int N, long iters) {
    make_base(p);
    pick_group(N);
    if (GN < d) return 0;
    random_voltages();
    long bad = eval_bad();
    const double T0 = 1.0, T1 = 0.05;
    for (long it = 0; it < iters && bad > 0; it++) {
        if ((it & 255) == 0 && now() > t_stop) break;
        int t = rndint(ND);
        int old = dg[t];
        int ng = rndint(GN);
        if (ng == old) continue;
        dg[t] = ng;
        if (clash(t, ng)) { dg[t] = old; continue; }
        long nb = eval_bad();
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) bad = nb;
        else dg[t] = old;
    }
    if (bad != 0) return 0;
    int n = 2 * P * GN;
    int m = build_lift_edges(teu, tev);
    if (n > best_n) consider(n, m, teu, tev);
    return 1;
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
    t_stop = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start();

    long moore = moore_bound();
    while (now() < t_stop && best_n < moore) {
        int r = rndint(10);
        int p = r < 5 ? 1 : r < 8 ? 2 : r < 9 ? 3 : 4;
        int Nmin = best_n / (2 * p) + 1;
        int N = Nmin + rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > MAXN || 2L * p * N > moore) continue;
        try_restart(p, N, 30000);
    }

    if (best_n == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", beu[e], bev[e]);
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

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.82 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
