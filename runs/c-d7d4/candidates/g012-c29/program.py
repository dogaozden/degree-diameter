import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (unchanged from parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared Python helpers (unchanged from parent, used for the start graph).
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
            for attempt in range(200):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
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
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW: C engine. Simulated annealing over degree-preserving bipartite switches,
# with greedy-cover vertex insertion.
#
# Invariant: the current graph is bipartite with max degree <= d. The cost is
# the number of vertex pairs at distance > D (computed exactly with bitset balls).
# Loop:
#   * cost 0: save it as the best graph, then insert one vertex. The new vertex
#     sits on one side and is joined to a greedy cover of the other side's
#     radius-(D-1) balls, so it is within distance D of everything. Saturated
#     neighbours give up one random edge. Then deficient cross pairs are joined.
#   * cost > 0: anneal with double-edge switches (degrees and bipartiteness kept).
#   * stall: after STALL moves without reaching cost 0, restore the best graph
#     and try a different random insertion.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 2048
#define MAXDEG 64
#define WS 32
#define STALL 100000L

static int DEG, DIAM, N, Wd;
static int adj[MAXN][MAXDEG];
static int deg[MAXN];
static int col[MAXN];
static int bestAdj[MAXN][MAXDEG];
static int bestDeg[MAXN];
static int bestCol[MAXN];
static int bestN = 0;
static uint64_t BA[MAXN * WS];
static uint64_t BB[MAXN * WS];
static uint64_t rs = 88172645463325252ULL;
static int mvA, mvB, mvC, mvE;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int k) {
    return (int)(rnd64() % (uint64_t)k);
}

static double rndd(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int has_edge(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++)
        if (adj[u][k] == v) return 1;
    return 0;
}

static void rm_arc(int u, int v) {
    int k;
    for (k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    rm_arc(u, v);
    rm_arc(v, u);
}

/* Radius-r balls as bitsets (row stride WS). Returns pointer to the result. */
static uint64_t *balls(int r) {
    uint64_t *cur = BA, *nxt = BB, *t;
    int v, k, w, it;
    Wd = (N + 63) >> 6;
    for (v = 0; v < N; v++) {
        for (w = 0; w < Wd; w++) cur[v * WS + w] = 0;
        cur[v * WS + (v >> 6)] = 1ULL << (v & 63);
    }
    for (it = 0; it < r; it++) {
        for (v = 0; v < N; v++) {
            uint64_t *x = nxt + v * WS;
            const uint64_t *s = cur + v * WS;
            for (w = 0; w < Wd; w++) x[w] = s[w];
            for (k = 0; k < deg[v]; k++) {
                const uint64_t *y = cur + adj[v][k] * WS;
                for (w = 0; w < Wd; w++) x[w] |= y[w];
            }
        }
        t = cur;
        cur = nxt;
        nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable included). */
static long cost(void) {
    uint64_t *p = balls(DIAM);
    long bad = 0;
    int v, w, c;
    for (v = 0; v < N; v++) {
        c = 0;
        for (w = 0; w < Wd; w++) c += __builtin_popcountll(p[v * WS + w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Degree-preserving bipartite double-edge switch: a-b, c-e -> a-e, c-b (a, c on side 0). */
static int try_switch(void) {
    int a, c, b, e;
    a = rndi(N);
    c = rndi(N);
    if (col[a] != 0 || col[c] != 0 || a == c) return 0;
    if (deg[a] == 0 || deg[c] == 0) return 0;
    b = adj[a][rndi(deg[a])];
    e = adj[c][rndi(deg[c])];
    if (e == b || has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    mvA = a;
    mvB = b;
    mvC = c;
    mvE = e;
    return 1;
}

static void undo_switch(void) {
    del_edge(mvA, mvE);
    del_edge(mvC, mvB);
    add_edge(mvA, mvB);
    add_edge(mvC, mvE);
}

/* Join deficient opposite-side pairs (only shortens distances, keeps bipartite). */
static void fill(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0, i, j, v, t;
    for (v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    for (i = nr - 1; i > 0; i--) {
        j = rndi(i + 1);
        t = R[i]; R[i] = R[j]; R[j] = t;
    }
    for (i = nl - 1; i > 0; i--) {
        j = rndi(i + 1);
        t = L[i]; L[i] = L[j]; L[j] = t;
    }
    for (i = 0; i < nl; i++) {
        int a = L[i];
        for (j = 0; j < nr && deg[a] < DEG; j++) {
            int b = R[j];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex joined to a greedy cover of the radius-(DIAM-1) balls on the other side. */
static void insert_vertex(void) {
    static int marked[MAXN];
    uint64_t cov[WS];
    int chosen[MAXDEG];
    int nc = 0, c, v, s, w, step, best, t, g;
    double bestsc, sc;
    uint64_t *p;

    if (N >= MAXN - 2) return;
    c = rndi(2);
    p = balls(DIAM - 1);
    memset(marked, 0, sizeof marked);
    for (w = 0; w < WS; w++) cov[w] = 0;
    for (step = 0; step < DEG; step++) {
        best = -1;
        bestsc = -1.0;
        for (s = 0; s < N; s++) {
            if (col[s] == c || marked[s]) continue;
            g = 0;
            for (w = 0; w < Wd; w++)
                g += __builtin_popcountll(p[s * WS + w] & ~cov[w]);
            if (g == 0) continue;
            sc = g + 0.5 * rndd() + (deg[s] < DEG ? 0.6 : 0.0);
            if (sc > bestsc) {
                bestsc = sc;
                best = s;
            }
        }
        if (best < 0) break;
        marked[best] = 1;
        chosen[nc++] = best;
        for (w = 0; w < Wd; w++) cov[w] |= p[best * WS + w];
    }
    if (nc == 0) return;

    v = N;
    N++;
    Wd = (N + 63) >> 6;
    col[v] = c;
    deg[v] = 0;
    for (step = 0; step < nc; step++) {
        s = chosen[step];
        if (deg[s] >= DEG) {
            t = adj[s][rndi(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    fill();
}

static uint64_t bestSlot;

static void save_best(void) {
    memcpy(bestAdj, adj, sizeof adj);
    memcpy(bestDeg, deg, sizeof deg);
    memcpy(bestCol, col, sizeof col);
    bestN = N;
}

static void restore_best(void) {
    memcpy(adj, bestAdj, sizeof adj);
    memcpy(deg, bestDeg, sizeof deg);
    memcpy(col, bestCol, sizeof col);
    N = bestN;
    Wd = (N + 63) >> 6;
}

/* Reads "n m" + edges. n = 0 means: start from K_{DEG,DEG}. Returns 0 on bad input. */
static int read_graph(void) {
    int n, m, i, u, v, k;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 0) {
        if (DEG > 60) return 0;
        N = 2 * DEG;
        for (i = 0; i < N; i++) {
            deg[i] = 0;
            col[i] = (i < DEG) ? 0 : 1;
        }
        for (u = 0; u < DEG; u++)
            for (v = 0; v < DEG; v++)
                add_edge(u, DEG + v);
        return 1;
    }
    if (n > MAXN - 4) return 0;
    N = n;
    for (i = 0; i < n; i++) deg[i] = 0;
    for (i = 0; i < m; i++) {
        if (scanf("%d %d", &u, &v) != 2) return 0;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (has_edge(u, v)) return 0;
        if (deg[u] >= DEG || deg[v] >= DEG) return 0;
        add_edge(u, v);
    }
    /* Two-colour by BFS; reject odd cycles. */
    {
        static int q[MAXN];
        int head, tail, x;
        for (i = 0; i < n; i++) col[i] = -1;
        for (i = 0; i < n; i++) {
            if (col[i] != -1) continue;
            col[i] = 0;
            head = 0;
            tail = 0;
            q[tail++] = i;
            while (head < tail) {
                x = q[head++];
                for (k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (col[y] == -1) {
                        col[y] = 1 - col[x];
                        q[tail++] = y;
                    } else if (col[y] == col[x]) {
                        return 0;
                    }
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    double tl;
    long cur, nc, stall = 0, it = 0, delta;
    double T = 0.5;
    clock_t t0;
    int k, M, v, j;

    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (k = 0; k < 10; k++) rnd64();
    tl = atof(argv[4]);

    if (DEG < 2 || DEG > 60 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    if (!read_graph()) {
        printf("0 0\n");
        return 0;
    }
    cur = cost();
    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    save_best();

    t0 = clock();
    insert_vertex();
    fill();
    cur = cost();
    stall = 0;

    for (;;) {
        if ((it & 63) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
        it++;
        if (cur == 0) {
            save_best();
            if (N >= MAXN - 2) break;
            T = 0.3 + 0.4 * rndd();
            insert_vertex();
            fill();
            cur = cost();
            stall = 0;
            continue;
        }
        if (!try_switch()) continue;
        nc = cost();
        delta = nc - cur;
        if (delta <= 0 || rndd() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            undo_switch();
        }
        if (++stall > STALL) {
            restore_best();
            cur = 0;
            stall = 0;
        }
    }
    if (cur == 0) save_best();

    if (bestN <= 0) {
        printf("0 0\n");
        return 0;
    }
    M = 0;
    for (v = 0; v < bestN; v++)
        for (j = 0; j < bestDeg[v]; j++)
            if (bestAdj[v][j] > v) M++;
    printf("%d %d\n", bestN, M);
    for (v = 0; v < bestN; v++)
        for (j = 0; j < bestDeg[v]; j++)
            if (bestAdj[v][j] > v) printf("%d %d\n", v, bestAdj[v][j]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 2:
        base_n, base_e = best_n, list(best_e)
        base = None
        if D >= 4:
            base = _best_gq(d)
        if base is None and D >= 3:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

        # Short randomized twin/cover pipelines from the structured base.
        trial_end = start + 0.16 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # NEW: C simulated annealing with greedy-cover vertex insertion, from the best graph.
    if D >= 2 and d <= 60 and best_n >= 2:
        elapsed = time.monotonic() - start
        cbudget = 0.80 * time_limit - elapsed - 1.0
        if cbudget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget, 2)],
                                 stdin_graph=(best_n, best_e),
                                 timeout=cbudget + 8.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
