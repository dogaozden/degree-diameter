import math
import random
import time

import lib

# Search engine: C simulated annealing that grows a valid bipartite graph one vertex at a time.
# A new vertex joins the opposite side and takes d neighbours, and the cost is the number of
# vertex pairs at distance > D. Moves are edge add, remove, and rewire, all kept bipartite and
# within max degree d. Whenever the cost reaches 0 the state is saved and the graph grows again;
# otherwise the search restores the last saved graph and retries the insertion.

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define CAP_MIN 6000
#define STEP_LIMIT 30000L

static int DMAX, DIAM, N, CAP, WMAX;
static int *deg, *nb, *col, *defl, *cand, *be_u, *be_v, *bcol;
static int be_n, be_m;
static u64 *ra, *rb;
static u64 rs = 88172645463325252ULL;

typedef struct { int t, a, b; } Op;
static Op ops[8];
static int nops;

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int irand(int n) { return (int)(rnd() % (u64)n); }
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    const int *p = nb + u * DMAX;
    for (int i = 0; i < deg[u]; i++) if (p[i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    nb[u * DMAX + deg[u]++] = v;
    nb[v * DMAX + deg[v]++] = u;
}

static void rm_one(int u, int v) {
    int *p = nb + u * DMAX;
    for (int i = 0; i < deg[u]; i++) {
        if (p[i] == v) { p[i] = p[--deg[u]]; return; }
    }
}

static void del_edge(int u, int v) { rm_one(u, v); rm_one(v, u); }

static void apply_op(int t, int a, int b) {
    if (t) add_edge(a, b); else del_edge(a, b);
    ops[nops].t = t; ops[nops].a = a; ops[nops].b = b;
    nops++;
}

static void undo_ops(void) {
    while (nops > 0) {
        nops--;
        if (ops[nops].t) del_edge(ops[nops].a, ops[nops].b);
        else add_edge(ops[nops].a, ops[nops].b);
    }
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable pairs included). */
static long bad_count(void) {
    int W = (N + 63) / 64;
    u64 *cur = ra, *nxt = rb;
    memset(cur, 0, sizeof(u64) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            u64 *dst = nxt + (size_t)v * W;
            u64 *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(u64) * (size_t)W);
            const int *p = nb + v * DMAX;
            for (int i = 0; i < deg[v]; i++) {
                const u64 *s2 = cur + (size_t)p[i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s2[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    long covered = 0;
    for (int v = 0; v < N; v++) {
        const u64 *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) covered += pop64(s[w]);
    }
    return ((long)N * (long)N - covered) / 2;
}

/* Random local move. Returns 0 if no move was applied, otherwise the number of ops. */
static int propose(void) {
    int nd = 0;
    for (int v = 0; v < N; v++) if (deg[v] < DMAX) defl[nd++] = v;
    double r = urand();
    if (r < 0.35) {
        if (nd < 2) return 0;
        for (int t = 0; t < 20; t++) {
            int u = defl[irand(nd)], w = defl[irand(nd)];
            if (u != w && col[u] != col[w] && !has_edge(u, w)) {
                apply_op(1, u, w);
                return 1;
            }
        }
        return 0;
    } else if (r < 0.6) {
        int u = irand(N);
        if (deg[u] == 0) return 0;
        int v = nb[u * DMAX + irand(deg[u])];
        apply_op(0, u, v);
        return 1;
    } else {
        int u = irand(N);
        if (deg[u] == 0 || nd == 0) return 0;
        int v = nb[u * DMAX + irand(deg[u])];
        for (int t = 0; t < 20; t++) {
            int w = defl[irand(nd)];
            if (w != v && w != u && col[w] == col[v] && !has_edge(u, w)) {
                apply_op(0, u, v);
                apply_op(1, u, w);
                return 2;
            }
        }
        return 0;
    }
}

/* Add a vertex on a random side joined to DMAX opposite vertices (low degree first). */
static int insert_vertex(void) {
    if (N >= CAP) return 0;
    int c = irand(2);
    int x = N;
    deg[x] = 0;
    col[x] = c;
    int nc = 0;
    for (int v = 0; v < x; v++) if (col[v] != c) cand[nc++] = v;
    if (nc < DMAX) return 0;
    N = x + 1;
    for (int k = 0; k < DMAX; k++) {
        int bi = k;
        for (int j = k + 1; j < nc; j++) {
            int dj = deg[cand[j]], db = deg[cand[bi]];
            if (dj < db || (dj == db && (rnd() & 1))) bi = j;
        }
        int t = cand[k]; cand[k] = cand[bi]; cand[bi] = t;
        int y = cand[k];
        if (deg[y] >= DMAX) {
            int z = nb[y * DMAX + irand(deg[y])];
            del_edge(y, z);
        }
        add_edge(x, y);
    }
    return 1;
}

static void save_best(void) {
    be_n = N;
    be_m = 0;
    for (int v = 0; v < N; v++) {
        for (int i = 0; i < deg[v]; i++) {
            int u = nb[v * DMAX + i];
            if (v < u) { be_u[be_m] = v; be_v[be_m] = u; be_m++; }
        }
    }
    memcpy(bcol, col, sizeof(int) * (size_t)N);
}

static void restore_best(void) {
    N = be_n;
    for (int v = 0; v < N; v++) deg[v] = 0;
    memcpy(col, bcol, sizeof(int) * (size_t)N);
    for (int i = 0; i < be_m; i++) add_edge(be_u[i], be_v[i]);
}

static void print_edges_raw(int n, int m, const int *eu, const int *ev) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    double t_end = now() + budget;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 1 || DMAX < 1 || DIAM < 1) {
        printf("1 0\n");
        return 0;
    }
    int *eu = (int *)malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    int *ev = (int *)malloc(sizeof(int) * (size_t)(m0 > 0 ? m0 : 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { m0 = i; break; }
    }

    CAP = (n0 + 1 > CAP_MIN) ? n0 + 1 : CAP_MIN;
    WMAX = (CAP + 63) / 64;
    deg = (int *)calloc((size_t)CAP, sizeof(int));
    col = (int *)calloc((size_t)CAP, sizeof(int));
    nb = (int *)calloc((size_t)CAP * DMAX, sizeof(int));
    defl = (int *)calloc((size_t)CAP, sizeof(int));
    cand = (int *)calloc((size_t)CAP, sizeof(int));
    bcol = (int *)calloc((size_t)CAP, sizeof(int));
    be_u = (int *)calloc((size_t)CAP * DMAX, sizeof(int));
    be_v = (int *)calloc((size_t)CAP * DMAX, sizeof(int));
    ra = (u64 *)calloc((size_t)CAP * WMAX, sizeof(u64));
    rb = (u64 *)calloc((size_t)CAP * WMAX, sizeof(u64));

    N = n0;
    int ok = 1;
    for (int i = 0; i < m0 && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
        if (has_edge(u, v) || deg[u] >= DMAX || deg[v] >= DMAX) { ok = 0; break; }
        add_edge(u, v);
    }
    /* Bipartiteness check and 2-colouring. */
    if (ok) {
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int head = 0, tail = 0;
            cand[tail++] = s;
            while (head < tail && ok) {
                int u = cand[head++];
                for (int i = 0; i < deg[u]; i++) {
                    int w = nb[u * DMAX + i];
                    if (col[w] == -1) { col[w] = 1 - col[u]; cand[tail++] = w; }
                    else if (col[w] == col[u]) { ok = 0; break; }
                }
            }
        }
    }
    if (!ok || bad_count() != 0) {
        print_edges_raw(n0, m0, eu, ev);
        return 0;
    }

    save_best();
    while (now() < t_end) {
        if (!insert_vertex()) break;
        long cost = bad_count();
        long steps = 0;
        while (cost > 0 && steps < STEP_LIMIT) {
            if ((steps & 255) == 0 && now() >= t_end) break;
            steps++;
            double temp = 0.6 * (1.0 - (double)steps / (double)STEP_LIMIT) + 0.02;
            nops = 0;
            if (!propose()) continue;
            long nc = bad_count();
            long delta = nc - cost;
            if (delta <= 0 || urand() < exp(-(double)delta / temp)) cost = nc;
            else undo_ops();
            nops = 0;
        }
        if (cost == 0) {
            save_best();
        } else {
            restore_best();
            if (now() >= t_end) break;
        }
    }

    printf("%d %d\n", be_n, be_m);
    for (int i = 0; i < be_m; i++) printf("%d %d\n", be_u[i], be_v[i]);
    return 0;
}
'''


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

    A new vertex whose neighbours' radius-(D-1) balls cover all vertices keeps the diameter <= D.
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
    """Add edges between opposite colour classes using spare degree (keeps bipartite and diameter)."""
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


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))

    cands = [lib.haar_graph(d, range(d))]   # K_{d,d}: diameter 2, always valid

    # Projective-plane base (diameter 3), extended into spare degree.
    if d >= 3:
        base = _pg_base(d)
        if base is not None:
            if D == 3 and lib.is_prime_power(d - 1):
                return _finish([base], d, D)   # Moore-extremal
            cands.append(base)
            aug = _augment(base[0], base[1], d, seed)
            cands.append(aug)
            cands.append(_extend(aug[0], aug[1], d, D, rng, min(deadline, time.monotonic() + 0.5)))

    # Araujo-Pardo & Lopez record construction (diameter 3, degree q+2 = d).
    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            al = lib.araujo_lopez_graph(d - 2)
            cands.append(al)
            aug = _augment(al[0], al[1], d, seed)
            cands.append(aug)
            cands.append(_extend(aug[0], aug[1], d, D, rng, min(deadline, time.monotonic() + 0.5)))
        except Exception:
            pass

    best = _finish(cands, d, D)

    # Growth-and-repair search in C, starting from the best valid graph found so far.
    remaining = deadline - time.monotonic()
    if D >= 3 and remaining > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining - 1.5, 2)],
                            stdin_graph=best, timeout=remaining + 5.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    return best
