"""Exhaustive bi-Cayley search plus lifts and growth, for d-regular bipartite graphs of diameter D.

Stage 1 enumerates every connection set (with identity included, which is WLOG) for every
candidate group of order N, checking the lift Cay-bi(G, S) with a two-source BFS. The largest
order that works wins. Stage 2 runs random multi-base voltage lifts (p = 2..4) over the same
groups. Stage 3 grows the best graph by two vertices per step with swap annealing. Python builds
algebraic starts (PG(2,q), Araujo-Pardo-Lopez, W(q), K_{d,d}), enumerates the group list, and
validates every returned graph before returning it.
"""
import itertools
import math
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

#define MAXN 4096
#define MAXD 16
#define MAXP 4
#define MAXG 256
#define MAXGROUPS 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

/* Semidirect Z_m x|_r Z_k, times Z_c. Element index ((a*k+b)*c + t). */
typedef struct {
    int m, k, r, c, N;
    int rp[MAXG];
} Grp;

typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static Grp groups[MAXGROUPS];
static int ngroups;
static int MUL[MAXG][MAXG];
static int INV[MAXG];
static Graph best;

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

static int gcd_int(int a, int b) {
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

static int gmul(const Grp *G, int x, int y) {
    int t1 = x % G->c, x1 = x / G->c;
    int t2 = y % G->c, y1 = y / G->c;
    int a1 = x1 / G->k, b1 = x1 % G->k;
    int a2 = y1 / G->k, b2 = y1 % G->k;
    int a = (int)((a1 + (long)G->rp[b1] * a2) % G->m);
    int b = (b1 + b2) % G->k;
    int t = (t1 + t2) % G->c;
    return (a * G->k + b) * G->c + t;
}

static int add_group(int m, int k, int r, int c) {
    if (ngroups >= MAXGROUPS) return 0;
    if (m < 1 || k < 1 || c < 1) return 0;
    int N = m * k * c;
    if (N < 1 || N > MAXG || k > MAXG) return 0;
    if (m > 1 && (r < 1 || r >= m || gcd_int(r, m) != 1 || powmod(r, k, m) != 1 % m)) return 0;
    Grp *G = &groups[ngroups];
    G->m = m; G->k = k; G->r = (m > 1) ? r : 0; G->c = c; G->N = N;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % m);
    ngroups++;
    return 1;
}

static void make_group_tables(const Grp *G) {
    int N = G->N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) MUL[x][y] = gmul(G, x, y);
    for (int x = 0; x < N; x++) {
        INV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MUL[x][y] == 0) { INV[x] = y; break; }
    }
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

/* BFS from src, depth <= D. Returns the number of vertices reached. */
static int bstamp[MAXN], bdist[MAXN], bqueue[MAXN];
static int bcur = 0;

static int bfs_reach(const Graph *g, int src) {
    if (++bcur > 1000000000) { memset(bstamp, 0, sizeof bstamp); bcur = 1; }
    int head = 0, tail = 0;
    bstamp[src] = bcur;
    bdist[src] = 0;
    bqueue[tail++] = src;
    while (head < tail) {
        int v = bqueue[head++];
        int dv = bdist[v];
        if (dv >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bstamp[u] != bcur) {
                bstamp[u] = bcur;
                bdist[u] = dv + 1;
                bqueue[tail++] = u;
            }
        }
    }
    return tail;
}

/* Number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    long total = 0;
    for (int s = 0; s < g->n; s++) total += g->n - bfs_reach(g, s);
    return total / 2;
}

static int full_valid(const Graph *g) {
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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
                if (g->side[u] == 255) { g->side[u] = (unsigned char)(1 - g->side[v]); queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!full_valid(g)) g->n = 0;
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

/* ---- lifts over a group with p fibres per side (random base, hill-climbed voltages) ---- */

static void lift_build(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, (p + dt[t].j) * N + gmul(G, x, dt[t].g));
}

/* Orbit reduction: left multiplication is an automorphism transitive on each fibre, so BFS from
 * the 2p fibre representatives is enough. Returns the total number of unreached pairs. */
static long orbit_bad(const Graph *g, int p, int N) {
    long total = 0;
    for (int b = 0; b < 2 * p; b++) total += g->n - bfs_reach(g, b * N);
    return total;
}

static int fresh_g(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { ok = 0; break; }
        if (ok) return g;
    }
}

static int lift_try(Graph *out, int p, int N, const Grp *G, long steps, double until) {
    static Dart dt[MAXD * MAXP];
    int nd = 0;
    int perm[MAXP];
    if (N < d) return 0;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            dt[nd].i = i;
            dt[nd].j = perm[i];
            dt[nd].g = fresh_g(dt, nd, -1, i, perm[i], N);
            nd++;
        }
    }
    lift_build(out, p, N, G, dt, nd);
    long bad = orbit_bad(out, p, N);
    for (long s = 0; s < steps && bad > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_g(dt, nd, t, dt[t].i, dt[t].j, N);
        lift_build(out, p, N, G, dt, nd);
        long nb = orbit_bad(out, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    lift_build(out, p, N, G, dt, nd);
    return bad == 0;
}

static void lift_phase(double until) {
    static Graph lc;
    if (ngroups == 0) return;
    long moore = moore_bound();
    while (now() < until) {
        int p = 2 + rndint(3);
        const Grp *G = &groups[rndint(ngroups)];
        int N = G->N;
        if (N < d) continue;
        long V = 2L * p * N;
        if (V <= best.n || V > moore || V > MAXN) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_try(&lc, p, N, G, 20000, until) && full_valid(&lc) && lc.n > best.n) {
                copy_graph(&best, &lc);
                break;
            }
        }
    }
}

/* ---- exhaustive bi-Cayley search: vertices A_x (x < N) and B_y (N + y), A_x ~ B_{x s}, s in S.
 * Normalisation: S may be taken to contain the identity, so S = {0} u (d-1 other elements). */

static int ist[2 * MAXG], idist[2 * MAXG], iq[2 * MAXG];
static int icur = 0;

static int bi_ok(const int *S, int N) {
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        if (++icur > 1000000000) { memset(ist, 0, sizeof ist); icur = 1; }
        int head = 0, tail = 0;
        int s0 = (src == 0) ? 0 : N;
        ist[s0] = icur; idist[s0] = 0; iq[tail++] = s0;
        while (head < tail) {
            int v = iq[head++];
            int dv = idist[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + MUL[v][S[i]];
                    if (ist[u] != icur) { ist[u] = icur; idist[u] = dv + 1; iq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = MUL[y][INV[S[i]]];
                    if (ist[u] != icur) { ist[u] = icur; idist[u] = dv + 1; iq[tail++] = u; }
                }
            }
        }
        if (tail < V) return 0;
    }
    return 1;
}

/* Returns 1 if a valid S was found, 0 if none exists, -1 on timeout. */
static int exhaustive(int N, double until, int *S) {
    int k = d - 1;
    if (N - 1 < k) return 0;
    int c[MAXD];
    for (int i = 0; i < k; i++) c[i] = i + 1;
    long cnt = 0;
    for (;;) {
        S[0] = 0;
        for (int i = 0; i < k; i++) S[i + 1] = c[i];
        if (bi_ok(S, N)) return 1;
        if ((++cnt & 4095) == 0 && now() > until) return -1;
        int i = k - 1;
        while (i >= 0 && c[i] == N - 1 - (k - 1 - i)) i--;
        if (i < 0) return 0;
        c[i]++;
        for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    }
}

static void exhaustive_phase(double until) {
    static int order[MAXGROUPS];
    static Graph tg;
    int no = 0;
    for (int g = 0; g < ngroups; g++) order[no++] = g;
    /* Sort by order, largest first. */
    for (int a = 1; a < no; a++) {
        int x = order[a], b = a - 1;
        while (b >= 0 && groups[order[b]].N < groups[x].N) { order[b + 1] = order[b]; b--; }
        order[b + 1] = x;
    }
    int S[MAXD];
    for (int q = 0; q < no && now() < until; q++) {
        const Grp *G = &groups[order[q]];
        int N = G->N;
        if (2 * N <= best.n || N - 1 < d - 1) continue;
        make_group_tables(G);
        int r = exhaustive(N, until, S);
        if (r == 1) {
            tg.n = 2 * N;
            for (int v = 0; v < tg.n; v++) { tg.deg[v] = 0; tg.side[v] = (unsigned char)(v >= N); }
            for (int x = 0; x < N; x++)
                for (int i = 0; i < d; i++) add_edge(&tg, x, N + MUL[x][S[i]]);
            if (tg.n > best.n && full_valid(&tg)) copy_graph(&best, &tg);
        }
        if (r < 0) break;
    }
}

/* ---- growth: add one vertex per side, then anneal degree-preserving swaps ---- */

static int anneal(Graph *w, double until) {
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 7) == 0 && now() > until) return 0;
        int v = rndint(w->n);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (s == v || w->side[s] != w->side[v] || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        del_edge(w, v, u);
        del_edge(w, s, t);
        add_edge(w, v, t);
        add_edge(w, s, u);
        long nb = bad_pairs(w);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(w, v, t);
            del_edge(w, s, u);
            add_edge(w, v, u);
            add_edge(w, s, t);
        }
        T *= 0.999;
        if (T < 0.05) T = 1.0;
    }
    return 1;
}

static int grow_once(const Graph *cg, Graph *w, double until) {
    int n = cg->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(w, cg);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = 0; w->deg[y] = 0;
    w->side[x] = 0; w->side[y] = 1;
    add_edge(w, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = stamp;
        used[b] = stamp;
        k++;
    }
    if (k < d - 1) return 0;
    return anneal(w, until);
}

static void grow_phase(double until) {
    static Graph cg, wk;
    copy_graph(&cg, &best);
    while (now() < until && cg.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 3.0 ? left : (left / 3.0 > 3.0 ? left / 3.0 : 3.0);
        double dl = now() + slice;
        if (dl > until) dl = until;
        if (grow_once(&cg, &wk, dl)) {
            copy_graph(&cg, &wk);
            if (cg.n > best.n) copy_graph(&best, &cg);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit ngroups [m k r c]... < start_graph\n");
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int ng = atoi(argv[5]);
    if (d < 1 || d > MAXD - 1 || D < 1 || ng < 0 || argc < 6 + 4 * ng) return 2;

    ngroups = 0;
    for (int g = 0; g < ng; g++)
        add_group(atoi(argv[6 + 4 * g]), atoi(argv[7 + 4 * g]),
                  atoi(argv[8 + 4 * g]), atoi(argv[9 + 4 * g]));

    double t0 = now();
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    read_start(&best);
    if (best.n <= 0) complete_bipartite(&best);

    double tot = t_end - t0;
    exhaustive_phase(t0 + 0.4 * tot);
    lift_phase(t0 + 0.6 * tot);
    if (best.n + 2 <= moore_bound()) grow_phase(t_end);

    if (!full_valid(&best)) complete_bipartite(&best);
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


def _groups(lo, hi, cap):
    """Group descriptors (m, k, r, c) with orders in [lo, hi], largest order first.
    Each describes Z_m x|_r Z_k times Z_c, of order m*k*c."""
    out, seen = [], set()
    for N in range(hi, lo - 1, -1):
        for c in range(1, N + 1):
            if N % c:
                continue
            base = N // c
            for m in range(1, base + 1):
                if base % m:
                    continue
                k = base // m
                if m == 1:
                    rs = [1]
                else:
                    rs = [r for r in range(1, m)
                          if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
                for r in rs:
                    key = (m, k, r, c)
                    if key in seen:
                        continue
                    seen.add(key)
                    out.append(key)
                    if len(out) >= cap:
                        return out
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
    try:
        for n, e in known_starts(d, D):
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
    except Exception:
        pass

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
        return best

    lo = max(d, best[0] // 8)
    hi = min(120, lib.moore_bound(d, D) // 2)
    groups = _groups(lo, hi, 800) if hi >= lo else []

    args = [d, D, seed, round(budget, 2), len(groups)]
    for g in groups:
        args.extend(g)
    try:
        text = lib.run_c(C_SOURCE, args, stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
