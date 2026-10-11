"""Bold variant: exhaustive Haar-graph search over semidirect groups, then voltage lifts over
p = 2..4 base vertices per side. Both run in C. Python builds the algebraic start and keeps a
validated fallback, so every returned graph is valid."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: Haar graphs, then voltage lifts.
 * Usage:  prog d D seed time_limit   < start_graph
 * stdin:  "n m" then m lines "u v", or "0 0".
 * stdout: "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (Haar graphs). For a group G of order N (semidirect Z_m x| Z_k), let
 *   a_x ~ b_y iff x^-1 y in S, with |S| = d and w.l.o.g. identity in S. Left multiplication is an
 *   automorphism that is transitive on each side, so diameter <= D needs only one BFS from an
 *   A-vertex and one from a B-vertex. All sets S are scanned when few, sampled otherwise.
 * Phase 2 (voltage lifts). Base: d-regular bipartite multigraph on p <= 4 + p vertices, given by
 *   darts (i, j, g). Hill-climb over voltages g and over j-endpoint swaps, with the orbit-reduced
 *   objective (BFS from the 2p fibre representatives).
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 32
#define MAXG 512
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXDART (MAXD * MAXP)
#define MAXGRP 4096
#define SET_CAP 200000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int m, k, r; } GDesc;

static int d, D;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered pairs at distance > D (bitset BFS). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static int is_valid(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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
    if (!is_valid(g)) g->n = 0;
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

/* ---------------------------------------------------------------- groups */

/* Group of order N = m*k: elements a*k+b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int MT[MAXG][MAXG];
static int INV[MAXG];
static int gN = 0;

/* All semidirect descriptors (m, k, r) with m*k = N, r^k = 1 mod m, gcd(r, m) = 1. */
static int list_groups(int N, GDesc *out, int cap) {
    int c = 0;
    for (int m = 1; m <= N && c < cap; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            out[c].m = 1; out[c].k = k; out[c].r = 0; c++;
            continue;
        }
        for (int r = 1; r < m && c < cap; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            out[c].m = m; out[c].k = k; out[c].r = r; c++;
        }
    }
    return c;
}

static void build_group(GDesc gd) {
    int m = gd.m, k = gd.k, r = gd.r;
    int N = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x][y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
    gN = N;
}

/* ------------------------------------------------------- phase 1: Haar */

static int S_el[MAXD];
static int adjU[2 * MAXG * MAXD];
static int distv[2 * MAXG], qv[2 * MAXG];
static Graph hg;

static void set_adj(void) {
    int N = gN;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) {
            adjU[x * d + t] = N + MT[x][S_el[t]];
            adjU[(N + x) * d + t] = MT[x][INV[S_el[t]]];
        }
}

/* True if every vertex is within distance D of src. */
static int reach_all(int src) {
    int V = 2 * gN;
    for (int v = 0; v < V; v++) distv[v] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int v = qv[head++];
        if (distv[v] >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = adjU[v * d + t];
            if (distv[u] < 0) { distv[u] = distv[v] + 1; qv[tail++] = u; }
        }
    }
    return tail == V;
}

/* Scan sets S = {0} u T, |T| = d-1, T subset of {1..N-1}. Leaves a successful S in S_el. */
static int search_sets(double until) {
    int N = gN, r = d - 1;
    double total = 1.0;
    for (int i = 0; i < r; i++) total = total * (N - 1 - i) / (i + 1);
    if (total <= SET_CAP) {
        int idx[MAXD];
        for (int i = 0; i < r; i++) idx[i] = i + 1;
        long it = 0;
        for (;;) {
            S_el[0] = 0;
            for (int i = 0; i < r; i++) S_el[i + 1] = idx[i];
            if ((++it & 1023) == 0 && now() > until) return 0;
            set_adj();
            if (reach_all(0) && reach_all(N)) return 1;
            int i = r - 1;
            while (i >= 0 && idx[i] == N - 1 - (r - 1 - i)) i--;
            if (i < 0) break;
            idx[i]++;
            for (int j = i + 1; j < r; j++) idx[j] = idx[j - 1] + 1;
        }
        return 0;
    }
    for (long s = 0; s < SET_CAP; s++) {
        if ((s & 1023) == 0 && now() > until) return 0;
        int c = 0;
        while (c < r) {
            int v = 1 + rndint(N - 1), dup = 0;
            for (int i = 0; i < c; i++)
                if (S_el[i + 1] == v) { dup = 1; break; }
            if (!dup) S_el[1 + c++] = v;
        }
        S_el[0] = 0;
        set_adj();
        if (reach_all(0) && reach_all(N)) return 1;
    }
    return 0;
}

static void build_haar(Graph *g) {
    int N = gN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) add_edge(g, x, N + MT[x][S_el[t]]);
}

static void haar_phase(Graph *best, double until) {
    long moore = moore_bound();
    int Nlo = best->n / 2 + 1;
    long Nhi = moore / 2;
    if (Nhi > MAXG - 1) Nhi = MAXG - 1;
    static GDesc gl[MAXGRP];
    for (int N = Nlo; N <= Nhi && now() < until; N++) {
        if (N - 1 < d - 1) continue;
        int ng = list_groups(N, gl, MAXGRP);
        for (int gi = 0; gi < ng && now() < until; gi++) {
            build_group(gl[gi]);
            if (search_sets(until)) {
                build_haar(&hg);
                if (is_valid(&hg) && hg.n > best->n) copy_graph(best, &hg);
                break;
            }
        }
    }
}

/* ------------------------------------------------------- phase 2: lifts */

static int lp, lN, lnd;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int sI[MAXDART], sJ[MAXDART], sG[MAXDART];
static Graph lg;
static int od[MAXN], oq[MAXN];

static void save_darts(void) {
    memcpy(sI, dI, sizeof(int) * lnd);
    memcpy(sJ, dJ, sizeof(int) * lnd);
    memcpy(sG, dG, sizeof(int) * lnd);
}

static void restore_darts(void) {
    memcpy(dI, sI, sizeof(int) * lnd);
    memcpy(dJ, sJ, sizeof(int) * lnd);
    memcpy(dG, sG, sizeof(int) * lnd);
}

/* Fibre layout: A-fibre i, element x -> i*N + x; B-fibre j -> (p+j)*N + x. */
static void build_lift(Graph *g) {
    int p = lp, N = lN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < lnd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, p * N + dJ[t] * N + MT[x][dG[t]]);
}

/* No two darts may share (i, j, g): that would give a parallel edge. */
static int darts_ok(void) {
    for (int a = 0; a < lnd; a++)
        for (int b = 0; b < a; b++)
            if (dI[a] == dI[b] && dJ[a] == dJ[b] && dG[a] == dG[b]) return 0;
    return 1;
}

/* Orbit-reduced objective: pairs (rep, vertex) at distance > D, rep = element 0 of each fibre. */
static long orbit_bad(const Graph *g) {
    int p = lp, N = lN, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) od[v] = -1;
        int head = 0, tail = 0;
        od[src] = 0;
        oq[tail++] = src;
        while (head < tail) {
            int v = oq[head++];
            if (od[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (od[u] < 0) { od[u] = od[v] + 1; oq[tail++] = u; }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* d layers, each a random permutation of the p fibres, so the base is d-regular. */
static void random_darts(void) {
    int p = lp, N = lN;
    lnd = 0;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            dI[lnd] = i;
            dJ[lnd] = perm[i];
            dG[lnd] = 0;
            lnd++;
        }
    }
    for (int attempt = 0; attempt < 10000; attempt++) {
        for (int t = 0; t < lnd; t++) dG[t] = rndint(N);
        if (darts_ok()) return;
    }
}

static void lift_phase(Graph *best, double until) {
    long moore = moore_bound();
    static GDesc gl[MAXGRP];
    long infeasible = 0;
    while (now() < until) {
        int p = 2 + rndint(3);
        int N = best->n / (2 * p) + 1 + rndint(2);
        if (N < d) N = d;
        if (N > MAXG - 1 || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++infeasible > 1000000) return;
            continue;
        }
        int ng = list_groups(N, gl, MAXGRP);
        if (ng == 0) continue;
        build_group(gl[rndint(ng)]);
        lp = p;
        lN = N;
        random_darts();
        if (!darts_ok()) continue;
        build_lift(&lg);
        long bad = orbit_bad(&lg);
        long stall = 0;
        while (bad > 0 && stall < 40000 && now() < until) {
            stall++;
            save_darts();
            if (rnd01() < 0.7) {
                dG[rndint(lnd)] = rndint(N);
            } else {
                int t1 = rndint(lnd), t2 = rndint(lnd);
                if (t1 == t2) continue;
                int s = dJ[t1];
                dJ[t1] = dJ[t2];
                dJ[t2] = s;
            }
            if (!darts_ok()) { restore_darts(); continue; }
            build_lift(&lg);
            long nb = orbit_bad(&lg);
            if (nb <= bad || rnd01() < 0.002) {
                if (nb < bad) stall = 0;
                bad = nb;
            } else {
                restore_darts();
            }
        }
        if (bad == 0) {
            build_lift(&lg);
            if (is_valid(&lg) && lg.n > best->n) copy_graph(best, &lg);
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
    double t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 2 || D < 2 || d > MAXD) {
        read_start(&best);
        if (best.n == 0) { printf("1 0\n"); return 0; }
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0 || !is_valid(&best)) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        double span = t_end - t0;
        haar_phase(&best, t0 + 0.5 * span);
        lift_phase(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
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
