import random
import time

import lib

# C engine: starts from a valid graph and tries to add vertices. Each attempt inserts one
# vertex with d neighbours, then runs simulated annealing over degree-preserving edge swaps
# and edge additions, minimising the number of vertex pairs at distance > D. A zero-cost
# state is a valid larger graph and becomes the new snapshot. Failed attempts restore the snapshot.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define DMAX 64
#define W 32

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][DMAX];
    int side[MAXN];
    int lst[2][MAXN];
    int cnt[2];
} State;

static State G, SNAP;
static uint64_t RA[MAXN][W], RB[MAXN][W];
static uint64_t rs = 88172645463325252ULL;
static int DC, D;
static int pool[MAXN];
static unsigned char PC16[65536];

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (uint64_t)k); }
static double rndf(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int pc64(uint64_t x) {
    return PC16[x & 0xffff] + PC16[(x >> 16) & 0xffff] + PC16[(x >> 32) & 0xffff] + PC16[(x >> 48) & 0xffff];
}

static int has_edge(int u, int v) {
    for (int i = 0; i < G.deg[u]; i++) if (G.adj[u][i] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    G.adj[u][G.deg[u]++] = v;
    G.adj[v][G.deg[v]++] = u;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < G.deg[u]; i++)
        if (G.adj[u][i] == v) { G.adj[u][i] = G.adj[u][--G.deg[u]]; return; }
}
static void del_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* number of unordered pairs at distance > D */
static int bad_count(void) {
    int n = G.n, wd = (n + 63) >> 6;
    uint64_t (*cur)[W] = RA, (*nxt)[W] = RB, (*t)[W];
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt[v];
            memcpy(o, cur[v], sizeof(uint64_t) * wd);
            for (int i = 0; i < G.deg[v]; i++) {
                const uint64_t *s = cur[G.adj[v][i]];
                for (int w = 0; w < wd; w++) o[w] |= s[w];
            }
        }
        t = cur; cur = nxt; nxt = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < wd; w++) c += pc64(cur[v][w]);
        tot += n - c;
    }
    return (int)(tot / 2);
}

/* degree-preserving swap: edges A-B, C-E (A,C side 0) become A-E, C-B */
static int try_swap(int *pa, int *pb, int *pc, int *pe) {
    if (G.cnt[0] < 2) return 0;
    int A = G.lst[0][rndi(G.cnt[0])], C = G.lst[0][rndi(G.cnt[0])];
    if (A == C || G.deg[A] == 0 || G.deg[C] == 0) return 0;
    int B = G.adj[A][rndi(G.deg[A])], E = G.adj[C][rndi(G.deg[C])];
    if (B == E || has_edge(A, E) || has_edge(C, B)) return 0;
    del_edge(A, B); del_edge(C, E); add_edge(A, E); add_edge(C, B);
    *pa = A; *pb = B; *pc = C; *pe = E;
    return 1;
}
static void undo_swap(int a, int b, int c, int e) {
    del_edge(a, e); del_edge(c, b); add_edge(a, b); add_edge(c, e);
}

static int try_add(int *pa, int *pb) {
    if (G.cnt[0] == 0 || G.cnt[1] == 0) return 0;
    for (int t = 0; t < 30; t++) {
        int A = G.lst[0][rndi(G.cnt[0])], B = G.lst[1][rndi(G.cnt[1])];
        if (G.deg[A] < DC && G.deg[B] < DC && !has_edge(A, B)) {
            add_edge(A, B);
            *pa = A; *pb = B;
            return 1;
        }
    }
    return 0;
}

/* add a new vertex on a random side, joined to DC opposite vertices (stealing one edge if saturated) */
static void insert_vertex(void) {
    int c = rndi(2), o = 1 - c;
    if (G.cnt[o] == 0) return;
    int x = G.n++;
    G.side[x] = c;
    G.deg[x] = 0;
    G.lst[c][G.cnt[c]++] = x;
    int len = G.cnt[o];
    int k = DC < len ? DC : len;
    memcpy(pool, G.lst[o], sizeof(int) * len);
    for (int i = 0; i < k; i++) {
        int j = i + rndi(len - i);
        int t = pool[i]; pool[i] = pool[j]; pool[j] = t;
        int u = pool[i];
        if (G.deg[u] >= DC) {
            int w = G.adj[u][rndi(G.deg[u])];
            del_edge(u, w);
        }
        add_edge(x, u);
    }
}

static int anneal(int iters, int cur, double T0, double T1, double deadline) {
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && now() > deadline) break;
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int nc;
        if (rndi(10) < 8) {
            int a, b, c, e;
            if (!try_swap(&a, &b, &c, &e)) continue;
            nc = bad_count();
            if (nc <= cur || rndf() < exp(-(nc - cur) / T)) cur = nc;
            else undo_swap(a, b, c, e);
        } else {
            int a, b;
            if (!try_add(&a, &b)) continue;
            nc = bad_count();
            if (nc <= cur || rndf() < exp(-(nc - cur) / T)) cur = nc;
            else del_edge(a, b);
        }
    }
    return cur;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DC = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    double deadline = now() + limit;

    for (int i = 0; i < 65536; i++) PC16[i] = (i == 0) ? 0 : (unsigned char)(PC16[i >> 1] + (i & 1));

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = m = 0;
    if (n <= 0 || n > MAXN - 2 || DC < 1 || DC > DMAX || D < 1) {
        printf("0 0\n");
        return 0;
    }
    memset(&G, 0, sizeof G);
    G.n = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (G.deg[u] >= DC || G.deg[v] >= DC || has_edge(u, v)) continue;
        add_edge(u, v);
    }
    /* two-colour */
    static int col[MAXN], stk[MAXN];
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int i = 0; i < G.deg[u]; i++) {
                int v = G.adj[u][i];
                if (col[v] < 0) { col[v] = 1 - col[u]; stk[sp++] = v; }
            }
        }
    }
    for (int v = 0; v < n; v++) {
        G.side[v] = col[v];
        G.lst[col[v]][G.cnt[col[v]]++] = v;
    }

    int have = 0;
    int cur = bad_count();
    if (cur > 0) cur = anneal(4000 + 20 * G.n, cur, 2.0, 0.1, deadline);
    if (cur == 0) { SNAP = G; have = 1; }

    while (have && now() < deadline && G.n < MAXN - 1) {
        G = SNAP;
        insert_vertex();
        cur = bad_count();
        int K = 3000 + 20 * G.n;
        cur = anneal(K, cur, 2.0, 0.1, deadline);
        if (cur == 0) SNAP = G;
        else G = SNAP;
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int M = 0;
    for (int v = 0; v < SNAP.n; v++)
        for (int i = 0; i < SNAP.deg[v]; i++)
            if (SNAP.adj[v][i] > v) M++;
    printf("%d %d\n", SNAP.n, M);
    for (int v = 0; v < SNAP.n; v++)
        for (int i = 0; i < SNAP.deg[v]; i++)
            if (SNAP.adj[v][i] > v) printf("%d %d\n", v, SNAP.adj[v][i]);
    return 0;
}
"""

C_BUDGET_FRAC = 0.8     # fraction of time_limit given to the whole pipeline before the C engine ends
C_MAX_N = 1900          # larger starts are not handed to the C engine (its array cap is 2048)


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Return a proper 2-colouring (0/1 per vertex) of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices, each attached to a set cover of the current graph.

    A new vertex x with neighbour set N is within distance D of every old vertex iff the
    radius-(D-1) balls of N cover all vertices. Old pairs only get closer, so the diameter
    bound is preserved.
    """
    edges = list(edges)
    if D < 2 or n == 0:
        return n, edges
    color = _two_colour(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1

    while time.monotonic() < deadline:
        full = (1 << n) - 1
        balls = lib._balls(n, edges, D - 1)
        grown = False
        order = [0, 1] if rng.random() < 0.5 else [1, 0]
        for c in order:
            cand = [u for u in range(n) if color[u] == 1 - c and deg[u] < d]
            rng.shuffle(cand)
            covered, chosen = 0, []
            while covered != full and len(chosen) < d and cand:
                best_u, best_gain = -1, 0
                for u in cand:
                    g = (balls[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_u, best_gain = u, g
                if best_u < 0:
                    break
                chosen.append(best_u)
                covered |= balls[best_u]
                cand.remove(best_u)
            if covered == full and chosen:
                x = n
                n += 1
                color.append(c)
                deg.append(len(chosen))
                for u in chosen:
                    edges.append((u, x))
                    deg[u] += 1
                grown = True
                break
        if not grown:
            break
    return n, edges


def _augment(n, edges, d, seed):
    """Add edges between opposite colour classes using spare degree.

    Extra edges only shorten distances and keep the graph bipartite, so the diameter
    bound and bipartiteness are preserved.
    """
    rng = random.Random(seed + 7)
    color = _two_colour(n, edges)
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    side0 = [u for u in range(n) if color[u] == 0]
    side1 = [v for v in range(n) if color[v] == 1]
    new_edges = list(edges)
    for _ in range(3):
        us = [u for u in side0 if deg[u] < d]
        rng.shuffle(us)
        for u in us:
            if deg[u] >= d:
                continue
            cands = [v for v in side1 if deg[v] < d and v not in adj[u]]
            if not cands:
                continue
            v = rng.choice(cands)
            adj[u].add(v)
            adj[v].add(u)
            deg[u] += 1
            deg[v] += 1
            new_edges.append((u, v))
    return n, new_edges


def _finish(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d} is extremal for D = 2

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    if D == 3 and d >= 3:
        base = _pg_base(d)
        if base is not None:
            if lib.is_prime_power(d - 1):   # Moore-extremal, nothing to improve
                return _finish([base], d, D)
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            cands.append(aug)
            cands.append(_extend(aug[0], aug[1], d, D, rng, time.monotonic() + 1.0))

    start = _finish(cands, d, D)

    # Let the C engine grow the best valid start for the rest of the budget.
    budget = t0 + C_BUDGET_FRAC * time_limit - 1.0 - time.monotonic()
    if budget < 1.0 or d > 64 or start[0] > C_MAX_N:
        return start
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=start, timeout=budget + 10.0)
        n, e = lib.parse_graph_text(out)
    except (RuntimeError, ValueError):
        return start
    if n > start[0] and lib.is_valid(n, e, d, D):
        return n, e
    return start
