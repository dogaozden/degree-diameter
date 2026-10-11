"""Bold variant: a different search core for the weakest parent case (d4D5).

The C engine is rewritten around general-group voltage lifts. Base multigraphs have up to 4 vertices
per side and are d-regular. Moves change voltages, and also swap endpoints between darts, which
rewires the base. The group is drawn at random from abelian Z_a x Z_b and semidirect Z_a x|_r Z_b
for each episode, so non-cyclic groups are used. Lifts are annealed on an orbit-reduced diameter
cost: BFS from the 2p fibre representatives, implicit adjacency, no graph rebuild per move.
When a lift beats the current best, it seeds a grow-by-two annealer, so the grow phase still runs.

Safety: Python starts from the best algebraic graph and validates it. C output is validated again
in Python, and the start graph is returned whenever C fails or does not improve it.
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
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 1024
#define MAXP 4
#define MAXND (MAXP * MAXD)
#define MAXENT 20000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static Graph best, work, cand;

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

/* ---------- explicit graph utilities ---------- */

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

/* Number of unordered pairs at distance > D; fills badv[v]. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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

/* ---------- groups: abelian Z_a x Z_b and semidirect Z_a x|_r Z_b ---------- */

#define MAXT 1024
static int MT[MAXG][MAXG];
static int INV[MAXG];
static int GN;
static int rpw[MAXG];

typedef struct { int type, a, b, r; } GEnt;
static GEnt gents[MAXENT];

/* Element of Z_a x|_r Z_b is coded as u*b + v; (u,v)(u2,v2) = (u + r^v u2, v + v2). type 0: r unused. */
static int enum_groups(int N) {
    int c = 0;
    for (int a = 1; a <= N && c < MAXENT - 1; a++) {
        if (N % a) continue;
        int b = N / a;
        gents[c].type = 0; gents[c].a = a; gents[c].b = b; gents[c].r = 0; c++;
        if (a < 2) continue;
        for (int r = 1; r < a && c < MAXENT; r++) {
            if (gcd(r, a) != 1) continue;
            if (powmod(r, b, a) != 1 % a) continue;
            gents[c].type = 1; gents[c].a = a; gents[c].b = b; gents[c].r = r; c++;
        }
    }
    return c;
}

static void set_group(const GEnt *e) {
    int a = e->a, b = e->b;
    GN = a * b;
    if (e->type == 0) {
        for (int x = 0; x < GN; x++)
            for (int y = 0; y < GN; y++)
                MT[x][y] = ((x / b + y / b) % a) * b + (x % b + y % b) % b;
    } else {
        rpw[0] = 1 % a;
        for (int i = 1; i < b; i++) rpw[i] = (int)((long)rpw[i - 1] * e->r % a);
        for (int x = 0; x < GN; x++) {
            int p1 = x / b, q1 = x % b;
            for (int y = 0; y < GN; y++) {
                int p2 = y / b, q2 = y % b;
                MT[x][y] = (int)(((p1 + (long)rpw[q1] * p2) % a) * b + (q1 + q2) % b);
            }
        }
    }
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (MT[x][y] == 0) { INV[x] = y; break; }
}

/* ---------- voltage lifts with a d-regular base multigraph on p + p vertices ---------- */

static int nd;
static int di[MAXND], dj[MAXND], dg[MAXND];
static int RD[MAXP][MAXD], RDn[MAXP], CD[MAXP][MAXD], CDn[MAXP];
static int vis[MAXN], dep[MAXN], qbuf[MAXN];
static int vstamp = 0;

static int clash_all(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && dg[s] == g && di[s] == di[t] && dj[s] == dj[t]) return 1;
    return 0;
}

static void init_base(int p) {
    nd = 0;
    for (int k = 0; k < d; k++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            di[nd] = i; dj[nd] = perm[i]; dg[nd] = -1; nd++;
        }
    }
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(GN); } while (clash_all(t, g));
        dg[t] = g;
    }
}

static void index_darts(int p) {
    for (int i = 0; i < p; i++) { RDn[i] = 0; CDn[i] = 0; }
    for (int t = 0; t < nd; t++) {
        RD[di[t]][RDn[di[t]]++] = t;
        CD[dj[t]][CDn[dj[t]]++] = t;
    }
}

/* Orbit-reduced cost: BFS (radius D) from the 2p fibre identities; sum of unreached vertices.
 * Zero exactly when the lift has diameter <= D. Requires index_darts(p) to be current. */
static long eval_bad(int p, int N) {
    int V = 2 * p * N, PN = p * N;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        if (++vstamp > 2000000000) { memset(vis, 0, sizeof(vis)); vstamp = 1; }
        int head = 0, tail = 0;
        vis[src] = vstamp; dep[src] = 0; qbuf[tail++] = src;
        while (head < tail) {
            int v = qbuf[head++];
            int dv = dep[v];
            if (dv >= D) continue;
            if (v < PN) {
                int i = v / N, x = v % N;
                for (int k = 0; k < RDn[i]; k++) {
                    int t = RD[i][k];
                    int u = (p + dj[t]) * N + MT[x][dg[t]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; dep[u] = dv + 1; qbuf[tail++] = u; }
                }
            } else {
                int j = v / N - p, y = v % N;
                for (int k = 0; k < CDn[j]; k++) {
                    int t = CD[j][k];
                    int u = di[t] * N + MT[y][INV[dg[t]]];
                    if (vis[u] != vstamp) { vis[u] = vstamp; dep[u] = dv + 1; qbuf[tail++] = u; }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Simulated annealing over voltages and base endpoint swaps for the current group. */
static int anneal(int p, int N, long steps) {
    init_base(p);
    index_darts(p);
    long cur = eval_bad(p, N);
    for (long s = 0; s < steps && cur > 0; s++) {
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.03;
        if (rndint(10) < 7) {
            int t = rndint(nd);
            int g = rndint(GN);
            if (g == dg[t] || clash_all(t, g)) continue;
            int old = dg[t];
            dg[t] = g;
            long nb = eval_bad(p, N);
            if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
            else dg[t] = old;
        } else {
            int t = rndint(nd), q = rndint(nd);
            if (t == q || dj[t] == dj[q]) continue;
            int jt = dj[t], jq = dj[q];
            dj[t] = jq; dj[q] = jt;
            if (clash_all(t, dg[t]) || clash_all(q, dg[q])) { dj[t] = jt; dj[q] = jq; continue; }
            index_darts(p);
            long nb = eval_bad(p, N);
            if (nb <= cur || rnd01() < exp((double)(cur - nb) / T)) cur = nb;
            else { dj[t] = jt; dj[q] = jq; index_darts(p); }
        }
    }
    return cur == 0;
}

static void build_lift_graph(Graph *g, int p, int N) {
    int PN = p * N;
    g->n = 2 * PN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= PN; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, (p + dj[t]) * N + MT[x][dg[t]]);
}

static void lift_stage(double until) {
    int stall = 0;
    while (now() < until && stall < 300) {
        int target = best.n + 2;
        long moore = moore_bound();
        if (target > moore || target > MAXN) return;
        int p = 1 + rndint(MAXP);
        int N = (target + 2 * p - 1) / (2 * p) + rndint(3);
        if (N < d) N = d;
        if (N > MAXG || 2L * p * N > moore || 2 * p * N > MAXN) continue;
        int ng = enum_groups(N);
        if (ng == 0) continue;
        set_group(&gents[rndint(ng)]);
        if (anneal(p, N, 20000)) {
            build_lift_graph(&cand, p, N);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                stall = 0;
                continue;
            }
        }
        stall++;
    }
}

/* ---------- grow by two: add one vertex per side and anneal degree-preserving swaps ---------- */

static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return rndint(g->n);
    int a = list[rndint(c)], b = list[rndint(c)];
    return badv[a] >= badv[b] ? a : b;
}

static int used[MAXN], saved[MAXN];
static int ustamp = 0;

static int grow_try(const Graph *base, Graph *w, double until) {
    int n = base->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(w, base);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    ++ustamp;
    used[x] = used[y] = ustamp;
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == ustamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == ustamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = ustamp;
        k++;
    }
    long bad = bad_pairs(w);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = pick_bad_vertex(w);
        if (w->deg[v] == 0) continue;
        int u = w->adj[v][rndint(w->deg[v])];
        int s = rndint(w->n);
        if (w->side[s] != w->side[v] || s == v || w->deg[s] == 0) continue;
        int t = w->adj[s][rndint(w->deg[s])];
        if (t == u || has_edge(w, v, t) || has_edge(w, s, u)) continue;
        memcpy(saved, badv, sizeof(int) * w->n);
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
            memcpy(badv, saved, sizeof(int) * w->n);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(w);
}

static void grow_stage(double until) {
    while (now() < until && best.n + 2 <= moore_bound() && best.n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_try(&best, &work, now() + slice)) copy_graph(&best, &work);
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
    t_end = t0 + limit * 0.94;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_stage(t0 + (t_end - t0) * 0.55);
        grow_stage(t_end);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.5:
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
