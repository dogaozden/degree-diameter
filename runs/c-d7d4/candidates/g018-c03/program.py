import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 1400
#define NW ((NMAX + 63) / 64)

static int d, D, N, W;
static int *adj, *deg, *col;
static uint64_t *ballbuf, *tmpbuf;
static uint64_t rs;
static double t_end;

static uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u * d + i] == v) return 1;
    return 0;
}
static void add_edge(int u, int v) {
    adj[u * d + deg[u]++] = v;
    adj[v * d + deg[v]++] = u;
}
static void del_arc(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adj[u * d + i] == v) {
            adj[u * d + i] = adj[u * d + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void remove_edge(int u, int v) { del_arc(u, v); del_arc(v, u); }

/* Bitset of all vertices within distance r of each vertex, written to res. */
static void compute_ball(int r, uint64_t *res) {
    W = (N + 63) / 64;
    uint64_t *cur = res, *nxt = tmpbuf;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur + (size_t)adj[v * d + i] * W;
                for (int k = 0; k < W; k++) o[k] |= src[k];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    if (cur != res) memcpy(res, cur, sizeof(uint64_t) * (size_t)N * W);
}

/* Number of unordered pairs at distance greater than D (unreachable counts). */
static long long cost_full(void) {
    compute_ball(D, ballbuf);
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *b = ballbuf + (size_t)v * W;
        int c = 0;
        for (int k = 0; k < W; k++) c += popc(b[k]);
        tot += N - c;
    }
    return tot / 2;
}

/* Insert a vertex on side c, joined to a greedy cover (by radius D-1 balls) of the
   opposite side. Full neighbours give up one random edge to make room. */
static void add_vertex(int c) {
    compute_ball(D - 1, ballbuf);
    W = (N + 63) / 64;
    uint64_t unc[NW];
    memset(unc, 0, sizeof unc);
    for (int v = 0; v < N; v++) unc[v >> 6] |= 1ULL << (v & 63);
    static char used[NMAX];
    memset(used, 0, sizeof used);
    int chosen[256];
    int nc = 0;
    for (int pick = 0; pick < d && nc < 256; pick++) {
        int best = -1;
        long bsc = -(1L << 40);
        for (int u = 0; u < N; u++) {
            if (col[u] == c || used[u]) continue;
            const uint64_t *b = ballbuf + (size_t)u * W;
            int g = 0;
            for (int k = 0; k < W; k++) g += popc(b[k] & unc[k]);
            long sc = (long)g * 4 + rndi(3);
            if (deg[u] >= d) sc -= 3;
            if (sc > bsc) { bsc = sc; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nc++] = best;
        const uint64_t *b = ballbuf + (size_t)best * W;
        for (int k = 0; k < W; k++) unc[k] &= ~b[k];
    }
    int v = N;
    N++;
    col[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nc; i++) {
        int u = chosen[i];
        if (deg[u] >= d) {
            int w = adj[u * d + rndi(deg[u])];
            remove_edge(u, w);
        }
        add_edge(u, v);
    }
}

/* Remove vertex x; the last vertex is relabelled into slot x. */
static void remove_vertex(int x) {
    while (deg[x] > 0) remove_edge(x, adj[x * d]);
    int L = N - 1;
    if (x != L) {
        for (int i = 0; i < deg[L]; i++) {
            int w = adj[L * d + i];
            for (int j = 0; j < deg[w]; j++) {
                if (adj[w * d + j] == L) { adj[w * d + j] = x; break; }
            }
        }
        memcpy(adj + (size_t)x * d, adj + (size_t)L * d, sizeof(int) * d);
        deg[x] = deg[L];
        col[x] = col[L];
    }
    deg[L] = 0;
    N--;
}

/* Add cross-side edges between deficient vertices in random order. */
static void fill(void) {
    static int L0[NMAX], L1[NMAX];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) L0[n0++] = v; else L1[n1++] = v;
        }
    }
    for (int i = n0 - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = L0[i]; L0[i] = L0[j]; L0[j] = t;
    }
    for (int i = n1 - 1; i > 0; i--) {
        int j = rndi(i + 1); int t = L1[i]; L1[i] = L1[j]; L1[j] = t;
    }
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg[a] < d; j++) {
            int b = L1[j];
            if (deg[b] < d && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static int pick_side0(void) {
    for (int t = 0; t < 1000000; t++) {
        int v = rndi(N);
        if (col[v] == 0 && deg[v] > 0) return v;
    }
    return -1;
}

/* Degree-preserving bipartite double-edge switches, simulated annealing on bad pairs.
   Returns 1 if the cost reaches 0. */
static int anneal(int iters, double T0, double T1) {
    long long cur = cost_full();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && now() > t_end) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a = pick_side0();
        int c = pick_side0();
        if (a < 0 || c < 0 || a == c) continue;
        int b = adj[a * d + rndi(deg[a])];
        int e = adj[c * d + rndi(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        remove_edge(a, b);
        remove_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        long long nw = cost_full();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            remove_edge(a, e);
            remove_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    return cur == 0;
}

typedef struct { int N; int *adj, *deg, *col; } Snap;

static void snap_alloc(Snap *s) {
    s->adj = malloc(sizeof(int) * (size_t)NMAX * d);
    s->deg = malloc(sizeof(int) * NMAX);
    s->col = malloc(sizeof(int) * NMAX);
    s->N = 0;
}
static void snap_save(Snap *s) {
    s->N = N;
    memcpy(s->adj, adj, sizeof(int) * (size_t)N * d);
    memcpy(s->deg, deg, sizeof(int) * N);
    memcpy(s->col, col, sizeof(int) * N);
}
static void snap_load(const Snap *s) {
    N = s->N;
    memcpy(adj, s->adj, sizeof(int) * (size_t)N * d);
    memcpy(deg, s->deg, sizeof(int) * N);
    memcpy(col, s->col, sizeof(int) * N);
}

#define ITER_GROW 600
#define ITER_KILL 250

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    if (d < 1 || d > 64 || D < 2) { printf("0 0\n"); return 0; }

    double t0 = now();
    t_end = t0 + budget * 0.95 - 0.3;
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 88172645463325252ULL;
    if (!rs) rs = 1;

    adj = malloc(sizeof(int) * (size_t)NMAX * d);
    deg = calloc(NMAX, sizeof(int));
    col = calloc(NMAX, sizeof(int));
    ballbuf = malloc(sizeof(uint64_t) * (size_t)NMAX * NW);
    tmpbuf = malloc(sizeof(uint64_t) * (size_t)NMAX * NW);
    if (!adj || !deg || !col || !ballbuf || !tmpbuf) { printf("0 0\n"); return 0; }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n == 0) {
        N = 2 * d;
        for (int i = 0; i < d; i++) {
            for (int j = 0; j < d; j++) add_edge(i, d + j);
        }
        for (int j = 0; j < d; j++) col[d + j] = 1;
    } else {
        if (n < 1 || n > NMAX - 2 || m < 0) { printf("0 0\n"); return 0; }
        N = n;
        int bad = 0;
        for (int i = 0; i < m; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { bad = 1; break; }
            if (u < 0 || u >= N || v < 0 || v >= N || u == v ||
                deg[u] >= d || deg[v] >= d || has_edge(u, v)) { bad = 1; break; }
            add_edge(u, v);
        }
        if (bad) { printf("0 0\n"); return 0; }
        for (int v = 0; v < N; v++) col[v] = -1;
        static int stk[NMAX];
        for (int s = 0; s < N; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int sp = 0;
            stk[sp++] = s;
            while (sp) {
                int x = stk[--sp];
                for (int i = 0; i < deg[x]; i++) {
                    int y = adj[x * d + i];
                    if (col[y] < 0) { col[y] = 1 - col[x]; stk[sp++] = y; }
                    else if (col[y] == col[x]) bad = 1;
                }
            }
        }
        if (bad) { printf("0 0\n"); return 0; }
    }

    if (cost_full() > 0) anneal(20000, 0.5, 0.05);
    if (cost_full() > 0) { printf("0 0\n"); return 0; }

    Snap cur, best;
    snap_alloc(&cur);
    snap_alloc(&best);
    snap_save(&cur);
    snap_save(&best);

    while (now() < t_end) {
        if (N < NMAX - 2 && rndi(10) < 6) {
            add_vertex(rndi(2));
            fill();
            if (anneal(ITER_GROW, 0.7, 0.12)) {
                snap_save(&cur);
                if (N > best.N) snap_save(&best);
            } else {
                snap_load(&cur);
            }
        } else {
            int curN = cur.N;
            int k = (rndi(3) == 0) ? 2 : 1;
            for (int i = 0; i < k && N > 3; i++) remove_vertex(rndi(N));
            fill();
            if (anneal(ITER_KILL, 0.5, 0.08) && N >= curN - 1) {
                snap_save(&cur);
                if (N > best.N) snap_save(&best);
            } else {
                snap_load(&cur);
            }
        }
        if (cur.N < best.N - 3) {
            snap_load(&best);
            snap_save(&cur);
        }
    }

    snap_load(&best);
    if (cost_full() != 0) { printf("0 0\n"); return 0; }
    int cnt = 0;
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u * d + i] > u) cnt++;
    printf("%d %d\n", N, cnt);
    for (int u = 0; u < N; u++)
        for (int i = 0; i < deg[u]; i++) {
            int v = adj[u * d + i];
            if (v > u) printf("%d %d\n", u, v);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d and q <= 9."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 steps."""
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-side vertices in random order."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized start: optional twin duplication, saturation, then cover growth."""
    n, e = base_n, list(base_e)
    if rng.random() < 0.5:
        n, e = _duplicate_twins(n, e, d, rng)
    e = _saturate_edges(n, e, d, rng)
    return _grow(n, e, d, D, deadline, rng, attempts=30)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= target:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
        consider(n1, e1)

    # Randomized twin/saturation/cover starts from the structured base.
    trial_end = start + 0.16 * time_limit
    while time.monotonic() < trial_end and best_n < target:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # C engine: bitset-based insertion, kill-regrow LNS and degree-preserving annealing.
    elapsed = time.monotonic() - start
    budget = 0.80 * time_limit - elapsed - 1.0
    if D >= 2 and budget >= 2.0 and best_n < target:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                            stdin_graph=(best_n, best_e), timeout=budget + 5.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
