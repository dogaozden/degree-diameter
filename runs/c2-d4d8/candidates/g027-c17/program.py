"""Bi-lift search with variable fibre count and base-graph rewiring.

Construction: a bipartite lift with P fibres per side (P = 1..4) over a metacyclic group
Z_m x|_r Z_k of order N, so n = 2PN. The base is d random permutation layers between the
A-fibres and the B-fibres. Each attempt samples a group, voltages and base layers, then
anneals against an exact orbit-reduced diameter count (BFS from the 2P fibre identities).

Moves:
- single-dart and pair-dart voltage changes;
- base rewiring: swap the B-targets of two fibres inside one permutation layer (the base stays
  d-regular, so the lift stays d-regular);
- best-state restoration at the end of each anneal.

Orders are chosen to beat the record: when a record is supplied, half of the attempts aim at
the smallest order above max(record, best + 2). The last part of the budget grows the best
graph by two vertices per side with degree-preserving annealing. Every output is checked with
lib.is_valid in Python and replaces the fallback only if it is valid and strictly larger.

This version has not been run here. The Python fallback is the best algebraic start, so every
case still returns a valid graph even if the C search fails to compile or finds nothing.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long MOORE;
static long target_n = 0;
static double t_end;

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
}

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (bitset ball expansion). */
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
        badv[v] = n - c;
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Metacyclic group Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c, b + e). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static Grp G;

static int gmul(int x, int y) {
    int a = x / G.k, b = x % G.k, c = y / G.k, e = y % G.k;
    return (int)((a + (long)G.rp[b] * c) % G.m) * G.k + (b + e) % G.k;
}

static void set_group(int m, int k, int r) {
    G.m = m; G.k = k; G.r = r;
    G.rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G.rp[b] = (int)((long)G.rp[b - 1] * r % m);
}

/* Uniformly random metacyclic group of order N (reservoir sampling over all (m, r)). */
static int pick_group(int N) {
    long count = 1;
    int bm = 1, bk = N, br = 1;
    for (int m = 2; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    set_group(bm, bk, br);
    return 1;
}

/* Lift state: P fibres per side, group order NN, nd = P*d darts.
 * Dart t = s*P + i joins A-fibre i to B-fibre dj[t] with voltage dg[t];
 * for each layer s, dj restricted to that layer is a permutation of 0..P-1. */
static int P, NN, nd;
static int di[MAXDART], dj[MAXDART], dg[MAXDART];
static int bestdg[MAXDART], bestdj[MAXDART];

static void make_darts(void) {
    nd = P * d;
    for (int s = 0; s < d; s++) {
        int perm[MAXP];
        for (int i = 0; i < P; i++) perm[i] = i;
        for (int i = P - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < P; i++) {
            int t = s * P + i;
            di[t] = i;
            dj[t] = perm[i];
        }
    }
}

/* True if dart t duplicates another dart's (fibre pair, voltage). */
static int clashes(int t) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == dg[t]) return 1;
    return 0;
}

static void build_lift(Graph *g) {
    int S = P * NN;
    g->n = 2 * S;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= S; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NN; x++)
            add_edge(g, di[t] * NN + x, S + dj[t] * NN + gmul(x, dg[t]));
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Left multiplication is an automorphism acting regularly on each fibre, so the diameter is at
 * most D iff BFS from the identity of every fibre (2P sources) reaches everything within D. */
static long orbit_bad(const Graph *g) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * P; b++) {
        int src = b * NN;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Anneal voltages and base layers. Leaves the lowest-defect state in dg/dj and builds g. */
static long anneal(Graph *g, int maxit, double until) {
    int idx[2], odg[2], odj[2], nc;
    build_lift(g);
    long bad = orbit_bad(g);
    long bestbad = bad;
    memcpy(bestdg, dg, sizeof(int) * nd);
    memcpy(bestdj, dj, sizeof(int) * nd);
    double T = 2.0;
    for (int it = 0; it < maxit && bestbad > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        nc = 0;
        int kind = rndint(10);
        if (kind < 8 || P < 2) {
            int t = rndint(nd);
            idx[nc] = t; odg[nc] = dg[t]; odj[nc] = dj[t]; nc++;
            if (kind >= 5) {
                int t2 = rndint(nd);
                if (t2 != t) {
                    idx[nc] = t2; odg[nc] = dg[t2]; odj[nc] = dj[t2]; nc++;
                }
            }
            for (int k = 0; k < nc; k++) dg[idx[k]] = rndint(NN);
        } else {
            int s = rndint(d);
            int i1 = rndint(P), i2 = rndint(P - 1);
            if (i2 >= i1) i2++;
            int t1 = s * P + i1, t2 = s * P + i2;
            idx[0] = t1; odg[0] = dg[t1]; odj[0] = dj[t1];
            idx[1] = t2; odg[1] = dg[t2]; odj[1] = dj[t2];
            nc = 2;
            int tmp = dj[t1]; dj[t1] = dj[t2]; dj[t2] = tmp;
        }
        int ok = 1;
        for (int k = 0; k < nc && ok; k++)
            if (clashes(idx[k])) ok = 0;
        if (ok) {
            build_lift(g);
            long nb = orbit_bad(g);
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
                bad = nb;
                if (bad < bestbad) {
                    bestbad = bad;
                    memcpy(bestdg, dg, sizeof(int) * nd);
                    memcpy(bestdj, dj, sizeof(int) * nd);
                }
            } else {
                ok = 0;
            }
        }
        if (!ok) {
            for (int k = 0; k < nc; k++) {
                dg[idx[k]] = odg[k];
                dj[idx[k]] = odj[k];
            }
        }
        T *= 0.9995;
        if (T < 0.05) T = 2.0;
    }
    memcpy(dg, bestdg, sizeof(int) * nd);
    memcpy(dj, bestdj, sizeof(int) * nd);
    build_lift(g);
    return bestbad;
}

/* Repeated random group / base / annealing tries at fibre count p and group order N. */
static int attempt_order(Graph *best, int p, int N, double until) {
    static Graph cand;
    if (N < d || p < 1 || p > MAXP) return 0;
    P = p;
    NN = N;
    while (now() < until) {
        if (!pick_group(N)) return 0;
        make_darts();
        for (int t = 0; t < nd; t++) dg[t] = -1;
        int okinit = 1;
        for (int t = 0; t < nd && okinit; t++) {
            int tries = 0;
            do {
                dg[t] = rndint(N);
                tries++;
            } while (clashes(t) && tries < 200);
            if (clashes(t)) okinit = 0;
        }
        if (!okinit) continue;
        long bad = anneal(&cand, 20000, until);
        if (bad == 0 && cand.n > best->n && is_valid(&cand)) {
            copy_graph(best, &cand);
            return 1;
        }
    }
    return 0;
}

/* Search: half the attempts aim at the smallest order above max(target, best) with random p,
 * half climb adaptively from the current best. */
static void search(Graph *best, double until) {
    long step = 1;
    long LIM = MOORE < MAXN ? MOORE : MAXN;
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > LIM) return;
        int p = 1 + rndint(MAXP);
        long N;
        int adaptive;
        if (rndint(2) == 0) {
            long goal = (target_n > best->n) ? target_n : best->n + 2;
            N = (goal + 2L * p - 1) / (2L * p);
            adaptive = 0;
        } else {
            long S = best->n / 2 + step;
            N = (S + p - 1) / p;
            adaptive = 1;
        }
        if (N < d) N = d;
        if (2L * p * N > LIM) {
            if (++fails > 200) return;
            continue;
        }
        fails = 0;
        double left = until - now();
        double sl = left / 6;
        if (sl < 1.0) sl = 1.0;
        if (sl > 4.0) sl = 4.0;
        if (sl > left) sl = left;
        int ok = attempt_order(best, p, (int)N, now() + sl);
        if (adaptive) {
            if (ok) { if (step < 512) step *= 2; }
            else if (step > 1) step /= 2;
        }
    }
}

/* Final phase: insert one vertex per side and anneal degree-preserving swaps. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > MOORE || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= MOORE) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [target_n] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    target_n = (argc >= 6) ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    MOORE = moore_bound();
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && best.n < MOORE) {
        search(&best, t0 + (t_end - t0) * 0.85);
    }
    if (best.n + 2 <= MOORE) grow_search(&best, t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Best known orders (targets for the record-jump phase in C).
RECORDS = {(3, 3): 14, (4, 8): 2184}


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

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.5:
        return best
    target = RECORDS.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), target],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
