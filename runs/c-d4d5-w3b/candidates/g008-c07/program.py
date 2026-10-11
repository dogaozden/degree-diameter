"""Bi-Cayley search with a lift fallback, for the bipartite degree-diameter problem.

This version changes construction for the weakest target (d=4, D=5). The parent searched
Z_m x| Z_k voltage lifts with 1-4 base vertices per side and then ran annealing. This version
uses a different construction first:

1. Bi-Cayley graphs over every semidirect product Z_m x|_r Z_k of order N. Vertices a_x and
   b_y, with a_x ~ b_{x s} for s in a connection set S of size d containing the identity. The
   right-translation symmetry of S makes the identity WLOG. Left multiplication by the group is
   an automorphism acting transitively on each side, so the diameter test needs only two BFS
   runs, from a_e and b_e. Connection sets are enumerated exhaustively when there are few, and
   sampled otherwise. N ascends from the first order that could beat the current best.
2. Random multi-fibre voltage lifts (2 or 3 base vertices per side) over the same groups, with
   a hill-climb on an orbit-reduced diameter count, for the remaining time.

Every candidate is checked in C with a full validity test, and the output is validated again in
Python. The fallback is always a valid algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or
K_{d,d}).
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

#define MAXN 1024
#define MAXD 16
#define MAXG 512
#define MAXP 3
#define GCAP 2048
#define CAP 100000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static int GM[MAXG][MAXG];
static int GI[MAXG];
static Graph best;
static Dart dt[MAXD * MAXP];
static int nd;
static int base_M[MAXP][MAXP];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* Full validity check: degree, simple, bipartite, diameter <= D (BFS from every vertex). */
static int valid_graph(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    static int dist[MAXN], q[MAXN];
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s] = 0;
        q[t++] = s;
        while (h < t) {
            int v = q[h++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist[u] < 0) { dist[u] = dist[v] + 1; q[t++] = u; }
            }
        }
        if (t < n) return 0;
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= d || g->deg[v] >= d) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!valid_graph(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    int k = (D == 1) ? 1 : d;
    if (k < 1) k = 1;
    g->n = 2 * k;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k; }
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++) add_edge(g, a, k + b);
}

/* ---------------- groups Z_m x|_r Z_k, element a*k+b ---------------- */

static void build_group(int m, int k, int r) {
    int N = m * k;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GM[x][y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GM[x][y] == 0) { GI[x] = y; break; }
}

static int list_groups(int N, int gl[][3], int cap) {
    int c = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (c < cap) { gl[c][0] = 1; gl[c][1] = k; gl[c][2] = 0; c++; }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (c < cap) { gl[c][0] = m; gl[c][1] = k; gl[c][2] = r; c++; }
        }
    }
    return c;
}

/* ---------------- bi-Cayley search (p = 1) ---------------- */

/* Bi-Cayley graph: a_x ~ b_{x s} for s in S. Vertices a_x = x, b_y = N + y.
 * The group acts transitively on each side, so checking BFS from a_e and b_e suffices. */
static int cay_ok(int N, const int *S) {
    static int dist[MAXN], q[MAXN];
    int nv = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int h = 0, t = 0;
        dist[s0] = 0;
        q[t++] = s0;
        while (h < t) {
            int v = q[h++];
            int dv = dist[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int k = 0; k < d; k++) {
                    int u = N + GM[v][S[k]];
                    if (dist[u] < 0) { dist[u] = dv + 1; q[t++] = u; }
                }
            } else {
                int y = v - N;
                for (int k = 0; k < d; k++) {
                    int u = GM[y][GI[S[k]]];
                    if (dist[u] < 0) { dist[u] = dv + 1; q[t++] = u; }
                }
            }
        }
        if (t < nv) return 0;
    }
    return 1;
}

static int install_cay(int N, const int *S) {
    static Graph cand;
    cand.n = 2 * N;
    for (int v = 0; v < 2 * N; v++) { cand.deg[v] = 0; cand.side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int k = 0; k < d; k++)
            add_edge(&cand, x, N + GM[x][S[k]]);
    if (cand.n > best.n && valid_graph(&cand)) { best = cand; return 1; }
    return 0;
}

static void pick_random_set(int N, int m1, int *S) {
    S[0] = 0;
    for (int i = 1; i <= m1; i++) {
        for (;;) {
            int v = 1 + rndint(N - 1), dup = 0;
            for (int j = 1; j < i; j++)
                if (S[j] == v) { dup = 1; break; }
            if (!dup) { S[i] = v; break; }
        }
    }
}

/* Search bi-Cayley graphs of order 2N. Returns 1 as soon as one is installed in best. */
static int cay_search_N(int N, double until) {
    static int gl[GCAP][3];
    int m1 = d - 1;
    if (N - 1 < m1) return 0;
    int ng = list_groups(N, gl, GCAP);
    for (int gi = 0; gi < ng; gi++) {
        if (now() > until) return 0;
        build_group(gl[gi][0], gl[gi][1], gl[gi][2]);
        int S[MAXD];
        S[0] = 0;
        double combos = 1.0;
        for (int i = 0; i < m1; i++) combos = combos * (N - 1 - i) / (i + 1);
        if (combos <= (double)CAP) {
            int c[MAXD];
            for (int i = 0; i < m1; i++) c[i] = i + 1;
            long cnt = 0;
            for (;;) {
                for (int i = 0; i < m1; i++) S[i + 1] = c[i];
                if ((++cnt & 1023) == 0 && now() > until) return 0;
                if (cay_ok(N, S) && install_cay(N, S)) return 1;
                int i = m1 - 1;
                while (i >= 0 && c[i] == (N - 1) - (m1 - 1 - i)) i--;
                if (i < 0) break;
                c[i]++;
                for (int j = i + 1; j < m1; j++) c[j] = c[j - 1] + 1;
            }
        } else {
            for (long s = 0; s < CAP; s++) {
                if ((s & 1023) == 0 && now() > until) return 0;
                pick_random_set(N, m1, S);
                if (cay_ok(N, S) && install_cay(N, S)) return 1;
            }
        }
    }
    return 0;
}

static void cay_phase(double until) {
    long moore = moore_bound();
    long N = best.n / 2 + 1;
    if (N < d) N = d;
    while (now() < until) {
        if (2 * N > moore || N > MAXG || 2 * N > MAXN) break;
        if (cay_search_N((int)N, until)) N = best.n / 2 + 1;
        else N++;
    }
}

/* ---------------- multi-fibre voltage lifts (p = 2 or 3) ---------------- */

static void make_base(int p) {
    for (;;) {
        memset(base_M, 0, sizeof base_M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) base_M[i][perm[i]]++;
        }
        int seen[2 * MAXP], st[2 * MAXP], top = 0, ns = 1;
        memset(seen, 0, sizeof seen);
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && base_M[v][u - p]) : (u < p && base_M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) return;
    }
}

static int fresh_voltage(int upto, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < upto; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void build_lift(Graph *g, int p, int N) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GM[x][dt[t].g]);
}

static int obfs_dist[MAXN], obfs_q[MAXN];

/* Orbit-reduced count: BFS from the 2p fibre identities only. Zero iff diameter <= D. */
static long orbit_bad(const Graph *g, int p, int N) {
    long total = 0;
    int nv = g->n;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) obfs_dist[v] = -1;
        int h = 0, t = 0;
        obfs_dist[src] = 0;
        obfs_q[t++] = src;
        while (h < t) {
            int v = obfs_q[h++];
            int dv = obfs_dist[v];
            if (dv >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (obfs_dist[u] < 0) { obfs_dist[u] = dv + 1; obfs_q[t++] = u; }
            }
        }
        total += nv - t;
    }
    return total;
}

static long lift_try(Graph *g, int p, int N, double until) {
    make_base(p);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < base_M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = (c == 0) ? 0 : fresh_voltage(nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < 20000 && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N);
    return bad;
}

static void lift_phase(double until) {
    static Graph cand;
    static int gl[GCAP][3];
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(4) < 3 ? 2 : 3;
        long target = (long)best.n + 2;
        if (target > moore) return;
        long Nmin = (target + 2 * p - 1) / (2 * p);
        long N = Nmin + rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > MAXN || 2L * p * N > moore) continue;
        int ng = list_groups((int)N, gl, GCAP);
        if (ng == 0) continue;
        int gi = rndint(ng);
        build_group(gl[gi][0], gl[gi][1], gl[gi][2]);
        for (int a = 0; a < 3 && now() < until; a++) {
            long bad = lift_try(&cand, p, (int)N, until);
            if (bad == 0 && cand.n > best.n && valid_graph(&cand)) { best = cand; break; }
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
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("2 1\n0 1\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        double split = t0 + (t_end - t0) * 0.5;
        cay_phase(split);
        lift_phase(t_end);
    }
    if (!valid_graph(&best)) complete_bipartite(&best);
    print_graph(&best);
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

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
