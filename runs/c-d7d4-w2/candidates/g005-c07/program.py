import itertools
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW 16
#define MAXE 24576
#define STAGE 20000LL

static const double T0 = 1.0, T1 = 0.05;

static int d, D;
static int n, ne, W;
static int eu[MAXE], ev[MAXE];
static int color[MAXN];
static int deg[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t BX[MAXN][MAXW], BY[MAXN][MAXW];

static int bn = 0, bne = 0;
static int beu[MAXE], bev[MAXE], bcol[MAXN];

static double deadline;
static int timed_out = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int time_left(void) {
    if (!timed_out && now() > deadline) timed_out = 1;
    return !timed_out;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of ordered-free unordered pairs at distance > D (0 means diameter <= D). */
static long long cost(void) {
    uint64_t (*cur)[MAXW] = BX;
    uint64_t (*nxt)[MAXW] = BY;
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, sizeof(uint64_t) * (size_t)W);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
        for (int i = 0; i < ne; i++) {
            int a = eu[i], b = ev[i];
            uint64_t *na = nxt[a], *nb = nxt[b];
            const uint64_t *ca = cur[a], *cb = cur[b];
            for (int w = 0; w < W; w++) {
                na[w] |= cb[w];
                nb[w] |= ca[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        miss += n - c;
    }
    return miss / 2;
}

/* Degree-preserving bipartite double-edge switch on edges i=(a,b), j=(c,e) -> (a,e), (c,b). */
static int switch_move(int i, int j) {
    int a = eu[i], b = ev[i], c = eu[j], e = ev[j];
    if (a == c || b == e) return 0;
    if (adjm[a][e] || adjm[c][b]) return 0;
    adjm[a][b] = adjm[b][a] = 0;
    adjm[c][e] = adjm[e][c] = 0;
    adjm[a][e] = adjm[e][a] = 1;
    adjm[c][b] = adjm[b][c] = 1;
    ev[i] = e;
    ev[j] = b;
    return 1;
}

static void undo_switch(int i, int j) {
    int a = eu[i], e = ev[i], c = eu[j], b = ev[j];
    adjm[a][e] = adjm[e][a] = 0;
    adjm[c][b] = adjm[b][c] = 0;
    adjm[a][b] = adjm[b][a] = 1;
    adjm[c][e] = adjm[e][c] = 1;
    ev[i] = b;
    ev[j] = e;
}

/* Anneal bad-pair count to zero at fixed n. Returns 1 on success (state valid). */
static int run_stage(long long moves, double t0, double t1) {
    if (ne < 2) return 0;
    long long cur = cost();
    if (cur == 0) return 1;
    for (long long it = 0; it < moves; it++) {
        if ((it & 63) == 0 && !time_left()) return 0;
        double T = t0 * pow(t1 / t0, (double)it / (double)moves);
        int i = rndi(ne), j = rndi(ne);
        if (i == j) continue;
        if (!switch_move(i, j)) continue;
        long long nc = cost();
        long long delta = nc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            undo_switch(i, j);
        }
    }
    return 0;
}

/* Add two vertices v (side 0) and w (side 1) keeping every degree equal to d. */
static int grow2(void) {
    if (ne == 0 || n + 2 > MAXN || ne + d > MAXE) return 0;
    int v = n, w = n + 1;
    n += 2;
    color[v] = 0;
    color[w] = 1;
    deg[v] = 0;
    deg[w] = 0;
    int k = 0;
    long tries = 0;
    while (k < d - 1) {
        if (++tries > 200000) return 0;
        int i = rndi(ne);
        int a = eu[i], b = ev[i];
        if (adjm[a][w] || adjm[v][b]) continue;
        /* edge (a,b) becomes (a,w), and (v,b) is added: a and b keep their degree */
        adjm[a][b] = adjm[b][a] = 0;
        adjm[a][w] = adjm[w][a] = 1;
        adjm[v][b] = adjm[b][v] = 1;
        ev[i] = w;
        eu[ne] = v;
        ev[ne] = b;
        ne++;
        deg[v]++;
        deg[w]++;
        k++;
    }
    adjm[v][w] = adjm[w][v] = 1;
    eu[ne] = v;
    ev[ne] = w;
    ne++;
    deg[v]++;
    deg[w]++;
    return 1;
}

/* Greedily join deficient opposite-side vertices. */
static void fill(void) {
    for (int a = 0; a < n; a++) {
        if (color[a] != 0 || deg[a] >= d) continue;
        for (int b = 0; b < n && deg[a] < d; b++) {
            if (color[b] != 1 || deg[b] >= d || adjm[a][b]) continue;
            if (ne >= MAXE) return;
            eu[ne] = a;
            ev[ne] = b;
            ne++;
            adjm[a][b] = adjm[b][a] = 1;
            deg[a]++;
            deg[b]++;
        }
    }
}

static void load_best(void) {
    n = bn;
    ne = bne;
    memset(adjm, 0, sizeof adjm);
    for (int v = 0; v < n; v++) {
        deg[v] = 0;
        color[v] = bcol[v];
    }
    for (int i = 0; i < ne; i++) {
        eu[i] = beu[i];
        ev[i] = bev[i];
        adjm[eu[i]][ev[i]] = adjm[ev[i]][eu[i]] = 1;
        deg[eu[i]]++;
        deg[ev[i]]++;
    }
}

static void record(void) {
    if (n <= bn) return;
    bn = n;
    bne = ne;
    memcpy(beu, eu, sizeof(int) * (size_t)ne);
    memcpy(bev, ev, sizeof(int) * (size_t)ne);
    memcpy(bcol, color, sizeof(int) * (size_t)n);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    double t0 = now();
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    deadline = t0 + budget;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs) rs = 1;
    for (int k = 0; k < 10; k++) rnd64();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN || m0 < 0 || m0 > MAXE) {
        printf("0 0\n");
        return 0;
    }
    static int tu[MAXE], tv[MAXE];
    for (int k = 0; k < m0; k++) {
        if (scanf("%d %d", &tu[k], &tv[k]) != 2) {
            printf("0 0\n");
            return 0;
        }
        if (tu[k] < 0 || tu[k] >= n0 || tv[k] < 0 || tv[k] >= n0 || tu[k] == tv[k]) {
            printf("0 0\n");
            return 0;
        }
    }

    /* 2-colouring by propagation. */
    n = n0;
    ne = 0;
    for (int i = 0; i < n; i++) color[i] = -1;
    int bad = 0;
    for (int s = 0; s < n; s++) {
        if (color[s] >= 0) continue;
        color[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int k = 0; k < m0; k++) {
                int u = tu[k], v = tv[k];
                if (color[u] >= 0 && color[v] < 0) {
                    color[v] = 1 - color[u];
                    changed = 1;
                } else if (color[v] >= 0 && color[u] < 0) {
                    color[u] = 1 - color[v];
                    changed = 1;
                } else if (color[u] >= 0 && color[u] == color[v]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    for (int i = 0; i < n; i++) deg[i] = 0;
    memset(adjm, 0, sizeof adjm);
    for (int k = 0; k < m0; k++) {
        int u = tu[k], v = tv[k];
        if (color[u] == 1) {
            int t = u;
            u = v;
            v = t;
        }
        if (adjm[u][v]) {
            printf("0 0\n");
            return 0;
        }
        adjm[u][v] = adjm[v][u] = 1;
        eu[ne] = u;
        ev[ne] = v;
        ne++;
        deg[u]++;
        deg[v]++;
    }
    for (int i = 0; i < n; i++) {
        if (deg[i] > d) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Establish a valid starting graph at the input order. */
    if (cost() == 0) record();
    while (bn == 0 && time_left()) {
        if (run_stage(STAGE, T0, T1)) record();
    }
    if (bn == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Grow by two vertices from the best valid graph, repairing by annealing. */
    while (time_left()) {
        load_best();
        if (!grow2()) continue;
        fill();
        if (run_stage(STAGE, T0, T1)) record();
    }

    printf("%d %d\n", bn, bne);
    for (int i = 0; i < bne; i++) printf("%d %d\n", beu[i], bev[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions (carried over from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# Shared graph helpers.
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


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
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
    """Greedily add twins in random order while neighbours have spare degree."""
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
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Bold change: C annealer that grows a valid graph by two vertices at a time,
# keeping every degree exactly d, and repairs the diameter by degree-preserving
# bipartite switches. Restarts from the best valid graph after each failure.
# ----------------------------------------------------------------------------

def _c_search(n, edges, d, D, seed, budget):
    """Run the C annealer from a valid start graph; returns (n, edges) as produced by C."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 20.0)
    return lib.parse_graph_text(out)


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

    # Phase A: structured base plus short randomized growth pipelines.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.08 * time_limit, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.12 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase B: C annealing growth from the best valid graph.
    if D >= 2 and d >= 2 and best_n < lib.moore_bound(d, D):
        budget = 0.80 * time_limit - (time.monotonic() - start) - 2.0
        if budget > 2.0:
            try:
                seed_c = int(seed) & 0xFFFFFFFF
                n2, e2 = _c_search(best_n, best_e, d, D, seed_c, budget)
                consider(n2, e2)
            except (RuntimeError, ValueError, OSError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
