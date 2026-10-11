import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-based annealed growth with vertex kill / regrow (LNS).
#
# State: a bipartite graph with max degree d and a valid diameter-D cost of 0.
# Cost = number of unordered vertex pairs at distance > D, computed exactly by
# bitset ball expansion. Moves are degree-preserving double-edge switches
# accepted by simulated annealing. Growth adds a vertex and steals edges from
# full neighbours, then fills spare degree and anneals back to cost 0.
# Kill-and-regrow moves reshuffle the graph at fixed order. Only cost-0 states
# are kept, so the printed graph is always valid.
# ----------------------------------------------------------------------------
C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define MAXW 18
#define MAXD 64
#define ITERS 4000
#define EMAX 20000

typedef struct {
    int n;
    int col[MAXN];
    int deg[MAXN];
    int adj[MAXN][MAXD];
} State;

static int DMAX, RAD, N;
static int gcol[MAXN], gdeg[MAXN], gadj[MAXN][MAXD];
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static double T_START, T_LIMIT;
static time_t W_START;
static State CUR, BEST;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static double cpu_now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int time_up(void) {
    if (cpu_now() - T_START >= T_LIMIT) return 1;
    if ((double)(time(NULL) - W_START) >= T_LIMIT - 1.5) return 1;
    return 0;
}

/* Number of unordered pairs at distance > RAD. */
static long long cost_full(void) {
    int n = N, w = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)w);
    for (int v = 0; v < n; v++) cur[(size_t)v * w + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < RAD; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * w;
            const uint64_t *src = cur + (size_t)v * w;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < gdeg[v]; k++) {
                const uint64_t *s = cur + (size_t)gadj[v][k] * w;
                for (int i = 0; i < w; i++) dst[i] |= s[i];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * w;
        for (int i = 0; i < w; i++) c += pc64(s[i]);
        tot += n - c;
    }
    return tot / 2;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < gdeg[a]; k++)
        if (gadj[a][k] == b) return 1;
    return 0;
}

static void rem_half(int a, int b) {
    for (int k = 0; k < gdeg[a]; k++)
        if (gadj[a][k] == b) {
            gadj[a][k] = gadj[a][--gdeg[a]];
            return;
        }
}

static void del_e(int a, int b) {
    rem_half(a, b);
    rem_half(b, a);
}

static void add_e(int a, int b) {
    gadj[a][gdeg[a]++] = b;
    gadj[b][gdeg[b]++] = a;
}

static void save_state(State *s) {
    s->n = N;
    memcpy(s->col, gcol, sizeof(gcol));
    memcpy(s->deg, gdeg, sizeof(gdeg));
    memcpy(s->adj, gadj, sizeof(gadj));
}

static void load_state(const State *s) {
    N = s->n;
    memcpy(gcol, s->col, sizeof(gcol));
    memcpy(gdeg, s->deg, sizeof(gdeg));
    memcpy(gadj, s->adj, sizeof(gadj));
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

static int color_graph(void) {
    static int stk[MAXN];
    for (int v = 0; v < N; v++) gcol[v] = -1;
    for (int s = 0; s < N; s++) {
        if (gcol[s] != -1) continue;
        gcol[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp) {
            int u = stk[--sp];
            for (int k = 0; k < gdeg[u]; k++) {
                int v = gadj[u][k];
                if (gcol[v] == -1) {
                    gcol[v] = 1 - gcol[u];
                    stk[sp++] = v;
                } else if (gcol[v] == gcol[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* Add a vertex on a random side: take up to DMAX opposite-side vertices,
   spare-degree ones first; a full neighbour gives up one edge to the new vertex. */
static void grow_one(void) {
    if (N >= MAXN - 1) return;
    int s = rndi(2);
    int v = N++;
    gcol[v] = s;
    gdeg[v] = 0;
    int cand[MAXN], used[MAXN];
    int nc = 0;
    for (int u = 0; u < v; u++) {
        used[u] = 0;
        if (gcol[u] == 1 - s) cand[nc++] = u;
    }
    shuffle_int(cand, nc);
    int chosen = 0;
    for (int i = 0; i < nc && chosen < DMAX; i++) {
        int u = cand[i];
        if (gdeg[u] < DMAX) {
            add_e(u, v);
            used[u] = 1;
            chosen++;
        }
    }
    for (int i = 0; i < nc && chosen < DMAX; i++) {
        int u = cand[i];
        if (used[u] || gdeg[u] < DMAX) continue;
        int w = gadj[u][rndi(gdeg[u])];
        del_e(u, w);
        add_e(u, v);
        used[u] = 1;
        chosen++;
    }
}

/* Delete vertex x, moving the last vertex into its label. */
static void kill_one(void) {
    if (N <= 2) return;
    int x = rndi(N), y = N - 1;
    for (int k = 0; k < gdeg[x]; k++) rem_half(gadj[x][k], x);
    gdeg[x] = 0;
    if (x != y) {
        gcol[x] = gcol[y];
        gdeg[x] = gdeg[y];
        memcpy(gadj[x], gadj[y], sizeof(gadj[x]));
        for (int k = 0; k < gdeg[x]; k++) {
            int u = gadj[x][k];
            for (int j = 0; j < gdeg[u]; j++)
                if (gadj[u][j] == y) gadj[u][j] = x;
        }
    }
    gdeg[y] = 0;
    N--;
}

/* Greedy random addition of cross edges between deficient vertices. */
static void fill_edges(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (gdeg[v] < DMAX) {
            if (gcol[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle_int(L0, n0);
    shuffle_int(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && gdeg[a] < DMAX; j++) {
            int b = L1[j];
            if (gdeg[b] < DMAX && !has_edge(a, b)) add_e(a, b);
        }
    }
}

/* Degree-preserving switches minimising bad pairs. Returns 1 when cost reaches 0. */
static int anneal(int iters, double T0, double T1) {
    static int S0[MAXN];
    int nS0 = 0;
    for (int v = 0; v < N; v++)
        if (gcol[v] == 0 && gdeg[v] > 0) S0[nS0++] = v;
    long long cur = cost_full();
    if (cur == 0) return 1;
    if (nS0 < 2) return 0;
    for (int it = 0; it < iters; it++) {
        if (time_up()) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a = S0[rndi(nS0)], c = S0[rndi(nS0)];
        if (a == c) continue;
        int b = gadj[a][rndi(gdeg[a])];
        int e = gadj[c][rndi(gdeg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_e(a, b);
        del_e(c, e);
        add_e(a, e);
        add_e(c, b);
        long long nw = cost_full();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
            if (cur == 0) return 1;
        } else {
            del_e(a, e);
            del_e(c, b);
            add_e(a, b);
            add_e(c, e);
        }
    }
    return 0;
}

static void print_state(const State *s) {
    long long tot = 0;
    for (int v = 0; v < s->n; v++) tot += s->deg[v];
    printf("%d %lld\n", s->n, tot / 2);
    for (int v = 0; v < s->n; v++)
        for (int k = 0; k < s->deg[v]; k++) {
            int u = s->adj[v][k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD2F1A3ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }
    DMAX = d;
    RAD = D;
    T_LIMIT = tl;
    T_START = cpu_now();
    W_START = time(NULL);

    static int EU[EMAX], EV[EMAX];
    int n = 0, m = 0, ne = 0;
    if (scanf("%d %d", &n, &m) != 2) {
        n = 0;
        m = 0;
    }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (ne < EMAX) {
            EU[ne] = u;
            EV[ne] = v;
            ne++;
        }
    }

    N = 0;
    if (n <= 0) {
        if (2 * d > MAXN - 2) {
            printf("0 0\n");
            return 0;
        }
        N = 2 * d;
        for (int v = 0; v < N; v++) {
            gcol[v] = v < d ? 0 : 1;
            gdeg[v] = 0;
        }
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) add_e(a, d + b);
        if (cost_full() != 0) {
            printf("0 0\n");
            return 0;
        }
    } else {
        if (n > MAXN - 2) {
            printf("%d %d\n", n, ne);
            for (int i = 0; i < ne; i++) printf("%d %d\n", EU[i], EV[i]);
            return 0;
        }
        N = n;
        for (int v = 0; v < N; v++) gdeg[v] = 0;
        int ok = 1;
        for (int i = 0; i < ne && ok; i++) {
            int u = EU[i], v = EV[i];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) ok = 0;
            else if (has_edge(u, v) || gdeg[u] >= DMAX || gdeg[v] >= DMAX) ok = 0;
            else add_e(u, v);
        }
        if (!ok || !color_graph() || cost_full() != 0) {
            printf("%d %d\n", n, ne);
            for (int i = 0; i < ne; i++) printf("%d %d\n", EU[i], EV[i]);
            return 0;
        }
    }

    save_state(&CUR);
    save_state(&BEST);

    while (!time_up()) {
        load_state(&CUR);
        double r = rndu();
        int kill = 0, grows = 1;
        if (r >= 0.3) {
            kill = 1 + rndi(2);
            grows = kill;
        }
        for (int i = 0; i < kill; i++) kill_one();
        for (int i = 0; i < grows; i++) grow_one();
        fill_edges();
        if (anneal(ITERS, 2.0, 0.2)) {
            save_state(&CUR);
            if (CUR.n > BEST.n) save_state(&BEST);
        }
    }

    print_state(&BEST);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python constructions (structured starts and randomized twin pipelines).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
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
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if best_n >= moore:
        return best_n, list(best_e)

    # Structured base: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    if best_n >= moore:
        return best_n, list(best_e)

    # Randomized twin-duplication pipelines supply the start graph for the C search.
    trial_end = start + 0.22 * time_limit
    while time.monotonic() < trial_end:
        n, e = _trial(base_n, base_e, d, D, rng, trial_end)
        consider(n, e)

    # C annealed growth / LNS from the best valid graph found so far.
    elapsed = time.monotonic() - start
    budget = 0.86 * time_limit - elapsed - 1.0
    if budget >= 2.0 and D >= 2 and best_n < moore:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=(best_n, best_e), timeout=budget + 6.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
