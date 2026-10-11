import itertools
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1100
#define WMAX 18
#define MAXD 16
#define ITERS 300

typedef uint64_t u64;

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

static State S;
static State best;
static int dd, DIAM;
static u64 rs = 88172645463325252ULL;
static u64 R1[MAXN][WMAX], R2[MAXN][WMAX], R3[MAXN][WMAX];
static int PA[MAXN * MAXN / 4 + 4][2];
static int sw_a, sw_b, sw_c, sw_e;

#define N (S.n)
#define DEG (S.deg)
#define ADJ (S.adj)
#define COL (S.col)

static u64 rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd64() % (u64)k); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int contains(int x, int y) {
    for (int j = 0; j < DEG[x]; j++)
        if (ADJ[x][j] == y) return 1;
    return 0;
}

static void replace_nb(int x, int old, int nw) {
    for (int j = 0; j < DEG[x]; j++)
        if (ADJ[x][j] == old) { ADJ[x][j] = nw; return; }
}

static void drop_nb(int x, int y) {
    for (int j = 0; j < DEG[x]; j++)
        if (ADJ[x][j] == y) {
            ADJ[x][j] = ADJ[x][DEG[x] - 1];
            DEG[x]--;
            return;
        }
}

static void add_edge(int a, int b) {
    ADJ[a][DEG[a]++] = b;
    ADJ[b][DEG[b]++] = a;
}

/* out[v] = bitmask of vertices within distance r of v. out must be R1 or R3. */
static void reach_radius(int r, u64 out[][WMAX]) {
    int w = (N + 63) / 64;
    for (int v = 0; v < N; v++) {
        for (int k = 0; k < w; k++) out[v][k] = 0;
        out[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            for (int k = 0; k < w; k++) R2[v][k] = out[v][k];
            for (int j = 0; j < DEG[v]; j++) {
                const u64 *src = out[ADJ[v][j]];
                for (int k = 0; k < w; k++) R2[v][k] |= src[k];
            }
        }
        for (int v = 0; v < N; v++)
            for (int k = 0; k < w; k++) out[v][k] = R2[v][k];
    }
}

/* number of unordered pairs at distance > DIAM (unreachable counts as bad) */
static long cost_now(void) {
    reach_radius(DIAM, R1);
    int w = (N + 63) / 64;
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int k = 0; k < w; k++) c += popc(R1[v][k]);
        bad += N - c;
    }
    return bad / 2;
}

/* add cross-side edges between deficient vertices; never increases cost */
static void fill(void) {
    static int La[MAXN], Rb[MAXN];
    int na = 0, nb = 0;
    for (int v = 0; v < N; v++)
        if (DEG[v] < dd) {
            if (COL[v] == 0) La[na++] = v;
            else Rb[nb++] = v;
        }
    int np = 0;
    for (int i = 0; i < na; i++)
        for (int j = 0; j < nb; j++)
            if (!contains(La[i], Rb[j])) {
                PA[np][0] = La[i];
                PA[np][1] = Rb[j];
                np++;
            }
    for (int i = np - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t0 = PA[i][0], t1 = PA[i][1];
        PA[i][0] = PA[j][0];
        PA[i][1] = PA[j][1];
        PA[j][0] = t0;
        PA[j][1] = t1;
    }
    for (int i = 0; i < np; i++) {
        int a = PA[i][0], b = PA[i][1];
        if (DEG[a] < dd && DEG[b] < dd && !contains(a, b)) add_edge(a, b);
    }
}

static int pick_side0(void) {
    for (int t = 0; t < 1000; t++) {
        int v = rndint(N);
        if (COL[v] == 0 && DEG[v] > 0) return v;
    }
    return -1;
}

/* degree-preserving bipartite double-edge switch: a-b, c-e -> a-e, c-b */
static int do_switch(void) {
    int a = pick_side0(), c = pick_side0();
    if (a < 0 || c < 0 || a == c) return 0;
    int b = ADJ[a][rndint(DEG[a])];
    int e = ADJ[c][rndint(DEG[c])];
    if (b == e || contains(a, e) || contains(c, b)) return 0;
    replace_nb(a, b, e);
    replace_nb(e, c, a);
    replace_nb(c, e, b);
    replace_nb(b, a, c);
    sw_a = a; sw_b = b; sw_c = c; sw_e = e;
    return 1;
}

static void undo_switch(void) {
    int a = sw_a, b = sw_b, c = sw_c, e = sw_e;
    replace_nb(a, e, b);
    replace_nb(b, c, a);
    replace_nb(c, b, e);
    replace_nb(e, a, c);
}

/* simulated annealing on switches; returns 1 iff the state ends with cost 0 */
static int anneal(int iters, double T0, double T1) {
    fill();
    long cur = cost_now();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 63) {
            fill();
            cur = cost_now();
            if (cur == 0) break;
        }
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (!do_switch()) continue;
        long nc = cost_now();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else undo_switch();
    }
    return cur == 0;
}

/* delete vertex v, moving the last vertex into its slot */
static void remove_vertex(int v) {
    for (int j = 0; j < DEG[v]; j++) drop_nb(ADJ[v][j], v);
    DEG[v] = 0;
    int L = N - 1;
    if (v != L) {
        DEG[v] = DEG[L];
        memcpy(ADJ[v], ADJ[L], sizeof(ADJ[v]));
        COL[v] = COL[L];
        for (int j = 0; j < DEG[v]; j++) replace_nb(ADJ[v][j], L, v);
    }
    N = N - 1;
}

/* add a vertex of colour t joined to a greedy cover of the opposite side.
   Full-degree neighbours give up one edge. Returns 1 if added. */
static int add_vertex(int t) {
    if (N >= MAXN - 2) return 0;
    int o = 1 - t;
    int w = (N + 63) / 64;
    char used[MAXN];
    memset(used, 0, sizeof used);
    reach_radius(DIAM - 1, R3);
    u64 cov[WMAX];
    memset(cov, 0, sizeof cov);
    int chosen[MAXD];
    int nc = 0;
    int covered = 0;
    while (nc < dd && covered < N) {
        int best_s = -1;
        long bkey = -1;
        for (int s = 0; s < N; s++) {
            if (COL[s] != o || used[s]) continue;
            int g = 0;
            for (int k = 0; k < w; k++) g += popc(R3[s][k] & ~cov[k]);
            if (g == 0) continue;
            long key = (long)g * 4 + (DEG[s] < dd ? 2 : 0) + rndint(2);
            if (key > bkey) { bkey = key; best_s = s; }
        }
        if (best_s < 0) break;
        used[best_s] = 1;
        chosen[nc++] = best_s;
        covered = 0;
        for (int k = 0; k < w; k++) {
            cov[k] |= R3[best_s][k];
            covered += popc(cov[k]);
        }
    }
    if (covered < N) return 0;
    int v = N;
    N = N + 1;
    COL[v] = t;
    DEG[v] = 0;
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (DEG[s] < dd) {
            add_edge(s, v);
        } else {
            int j = rndint(DEG[s]);
            int tp = ADJ[s][j];
            ADJ[s][j] = v;
            drop_nb(tp, s);
            ADJ[v][DEG[v]++] = s;
        }
    }
    return 1;
}

static int read_input(void) {
    int n, m;
    if (scanf("%d %d", &n, &m) != 2) return 0;
    if (n <= 1 || n > MAXN - 2) return 0;
    N = n;
    memset(DEG, 0, sizeof(S.deg));
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (DEG[u] >= dd || DEG[v] >= dd || contains(u, v)) continue;
        add_edge(u, v);
    }
    static int queue[MAXN];
    for (int v = 0; v < N; v++) COL[v] = -1;
    for (int s = 0; s < N; s++) {
        if (COL[s] != -1) continue;
        COL[s] = 0;
        int head = 0, tail = 0;
        queue[tail++] = s;
        while (head < tail) {
            int x = queue[head++];
            for (int j = 0; j < DEG[x]; j++) {
                int y = ADJ[x][j];
                if (COL[y] == -1) {
                    COL[y] = 1 - COL[x];
                    queue[tail++] = y;
                } else if (COL[y] == COL[x]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

/* K_{d,d}: valid for diameter >= 2 */
static void build_kdd(void) {
    N = 2 * dd;
    memset(DEG, 0, sizeof(S.deg));
    for (int v = 0; v < N; v++) COL[v] = (v < dd) ? 0 : 1;
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++) add_edge(i, dd + j);
}

static void print_state(const State *s) {
    long m = 0;
    for (int v = 0; v < s->n; v++) m += s->deg[v];
    printf("%d %ld\n", s->n, m / 2);
    for (int v = 0; v < s->n; v++)
        for (int j = 0; j < s->deg[v]; j++)
            if (v < s->adj[v][j]) printf("%d %d\n", v, s->adj[v][j]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    for (int i = 0; i < 20; i++) rnd64();
    if (dd < 2 || dd > MAXD || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    clock_t t0 = clock();

    int have = read_input();
    if (have && cost_now() != 0) have = anneal(4000, 1.2, 0.05);
    if (!have) build_kdd();
    best = S;

    static State snap;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < tl) {
        snap = S;
        int kind = rndint(10);
        if (kind < 3) {
            add_vertex(rndint(2));
        } else {
            int k = 1 + rndint(3);
            for (int i = 0; i < k && N > 4; i++) remove_vertex(rndint(N));
            int g = k + (rndint(3) == 0 ? 1 : 0);
            for (int i = 0; i < g; i++) add_vertex(rndint(2));
        }
        if (!anneal(ITERS, 1.2, 0.05)) {
            S = snap;
            continue;
        }
        if (N > best.n) best = S;
        if (N < snap.n - 1 && rnd01() < 0.7) S = snap;
        else if (N + 3 < best.n) S = best;
    }
    print_state(&best);
    return 0;
}
'''


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
    """Generalized quadrangle incidence graph W(q), largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers (Python side: constructions and cheap growth only).
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
    """Greedily join deficient opposite-side vertices in random order (only shortens distances)."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree (keeps diameter)."""
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
    """One randomized Python pipeline: twin duplication mixed with cover growth."""
    mode = rng.randrange(2)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
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

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured bases: generalized quadrangle for D >= 4, projective plane for D = 3.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Calibration cases already at the Moore-type bound need no search.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Short randomized Python pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C engine: degree-preserving annealing with bitset cost, kill/regrow LNS,
    # and cover-based vertex insertion that steals edges from full neighbours.
    if D >= 2 and 2 <= d <= 15:
        elapsed = time.monotonic() - start
        budget = 0.86 * time_limit - elapsed - 3.0
        if budget > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 4.0)
                n2, e2 = lib.parse_graph_text(out)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
