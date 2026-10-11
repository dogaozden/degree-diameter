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

#define MAXN 4096
#define MAXD 64
#define MAXW ((MAXN + 63) / 64)
#define T_HOT 0.8
#define T_COLD 0.1

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    int col[MAXN];
} State;

typedef struct { int a, b, c, e; } Sw;

static State G, best_s, snap_s, tmp_s;
static int d_ = 1, D_ = 2;
static int W = 1;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static uint64_t rs = 88172645463325252ULL;
static clock_t c0;
static time_t w0;
static double budget = 1.0;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int m) {
    if (m <= 0) return 0;
    return (int)(rnd64() % (uint64_t)m);
}

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int timeup(void) {
    double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
    if (el >= budget) return 1;
    if (difftime(time(NULL), w0) >= budget + 1.0) return 1;
    return 0;
}

static void save_state(State *s) {
    int n = G.n;
    s->n = n;
    memcpy(s->deg, G.deg, sizeof(int) * n);
    memcpy(s->col, G.col, sizeof(int) * n);
    memcpy(s->adj, G.adj, sizeof(int) * MAXD * n);
}

static void load_state(const State *s) {
    int n = s->n;
    G.n = n;
    memcpy(G.deg, s->deg, sizeof(int) * n);
    memcpy(G.col, s->col, sizeof(int) * n);
    memcpy(G.adj, s->adj, sizeof(int) * MAXD * n);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++)
        if (G.adj[a][k] == b) return 1;
    return 0;
}

static void rem_nb(int a, int b) {
    for (int k = 0; k < G.deg[a]; k++) {
        if (G.adj[a][k] == b) {
            int last = --G.deg[a];
            G.adj[a][k] = G.adj[a][last];
            return;
        }
    }
}

static void add_edge(int a, int b) {
    G.adj[a][G.deg[a]++] = b;
    G.adj[b][G.deg[b]++] = a;
}

static void del_edge(int a, int b) {
    rem_nb(a, b);
    rem_nb(b, a);
}

/* Random bipartite double-edge switch: a-b, c-e  ->  a-e, c-b (a, c on side 0). */
static int propose_switch(Sw *s) {
    int n = G.n;
    for (int tries = 0; tries < 30; tries++) {
        int a = rndint(n);
        if (G.col[a] != 0 || G.deg[a] == 0) continue;
        int c = rndint(n);
        if (c == a || G.col[c] != 0 || G.deg[c] == 0) continue;
        int b = G.adj[a][rndint(G.deg[a])];
        int e = G.adj[c][rndint(G.deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        s->a = a; s->b = b; s->c = c; s->e = e;
        return 1;
    }
    return 0;
}

static void apply_switch(const Sw *s) {
    del_edge(s->a, s->b);
    del_edge(s->c, s->e);
    add_edge(s->a, s->e);
    add_edge(s->c, s->b);
}

static void undo_switch(const Sw *s) {
    del_edge(s->a, s->e);
    del_edge(s->c, s->b);
    add_edge(s->a, s->b);
    add_edge(s->c, s->e);
}

/* Bitset balls of radius r; returns the buffer holding them (BA or BB). */
static uint64_t *balls(int r) {
    int n = G.n;
    W = (n + 63) >> 6;
    uint64_t *cur = BA, *nx = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < G.deg[v]; k++) {
                const uint64_t *q = cur + (size_t)G.adj[v][k] * W;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
        }
        uint64_t *t = cur;
        cur = nx;
        nx = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > D_ (unreachable counts). */
static long long bad_pairs(void) {
    int n = G.n;
    uint64_t *b = balls(D_);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++)
            c += __builtin_popcountll(b[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void shuffle_int(int *x, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill_deficient(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < G.n; v++) {
        if (G.deg[v] >= d_) continue;
        if (G.col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && G.deg[a] < d_; j++) {
            int b = R[j];
            if (G.deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Simulated annealing on bad-pair count with degree-preserving switches. Returns final cost. */
static long long anneal(int iters, double T0, double T1) {
    long long cur = bad_pairs();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && timeup()) break;
        Sw s;
        if (!propose_switch(&s)) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        apply_switch(&s);
        long long nw = bad_pairs();
        long long delta = nw - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nw;
        else undo_switch(&s);
    }
    return cur;
}

/* Delete vertex x, moving the last vertex into its slot. */
static void remove_vertex(int x) {
    for (int k = 0; k < G.deg[x]; k++) {
        int y = G.adj[x][k];
        rem_nb(y, x);
    }
    G.deg[x] = 0;
    int last = G.n - 1;
    if (x != last) {
        int dl = G.deg[last];
        for (int k = 0; k < dl; k++) {
            int y = G.adj[last][k];
            for (int j = 0; j < G.deg[y]; j++) {
                if (G.adj[y][j] == last) {
                    G.adj[y][j] = x;
                    break;
                }
            }
        }
        memcpy(G.adj[x], G.adj[last], sizeof(int) * dl);
        G.deg[x] = dl;
        G.col[x] = G.col[last];
    }
    G.n = last;
}

/* Add one vertex on the side opposite to a greedily chosen cover of side s, then repair. */
static int op_add(int iters) {
    int n = G.n;
    if (n + 1 >= MAXN) return 0;
    int s = rndint(2);
    uint64_t *B = balls(D_ - 1);
    uint64_t cov[MAXW];
    memset(cov, 0, sizeof(uint64_t) * W);
    int chosen[MAXD];
    int nc = 0;
    for (int t = 0; t < d_; t++) {
        int best = -1;
        double bs = -1e18;
        for (int x = 0; x < n; x++) {
            if (G.col[x] != s) continue;
            int used = 0;
            for (int q = 0; q < nc; q++)
                if (chosen[q] == x) { used = 1; break; }
            if (used) continue;
            const uint64_t *bx = B + (size_t)x * W;
            int g = 0;
            for (int w = 0; w < W; w++)
                g += __builtin_popcountll(bx[w] & ~cov[w]);
            double sc = g + 0.9 * rnd01() - (G.deg[x] >= d_ ? 1.5 : 0.0);
            if (sc > bs) { bs = sc; best = x; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        const uint64_t *bb = B + (size_t)best * W;
        for (int w = 0; w < W; w++) cov[w] |= bb[w];
    }
    int v = n;
    G.n = n + 1;
    G.col[v] = 1 - s;
    G.deg[v] = 0;
    for (int q = 0; q < nc; q++) {
        int x = chosen[q];
        if (G.deg[x] >= d_) {
            int t = G.adj[x][rndint(G.deg[x])];
            del_edge(x, t);
        }
        add_edge(x, v);
    }
    fill_deficient();
    return anneal(iters, T_HOT, T_COLD) == 0;
}

/* Kill 1-3 vertices, repair, then regrow greedily. Result is valid on success. */
static int op_kill_regrow(void) {
    int k = 1 + rndint(3);
    for (int i = 0; i < k && G.n > 4; i++)
        remove_vertex(rndint(G.n));
    fill_deficient();
    if (anneal(1500, T_HOT, T_COLD) != 0) return 0;
    int fails = 0;
    while (fails < 3 && !timeup()) {
        save_state(&tmp_s);
        if (op_add(800)) fails = 0;
        else {
            load_state(&tmp_s);
            fails++;
        }
    }
    return 1;
}

/* Random switches (plateau move at fixed order), then repair. */
static int op_shake(void) {
    int k = 10 + rndint(30);
    for (int i = 0; i < k; i++) {
        Sw s;
        if (propose_switch(&s)) apply_switch(&s);
    }
    fill_deficient();
    return anneal(1500, T_HOT, T_COLD) == 0;
}

static int bipartite_colour(void) {
    static int st[MAXN];
    for (int v = 0; v < G.n; v++) G.col[v] = -1;
    for (int s = 0; s < G.n; s++) {
        if (G.col[s] != -1) continue;
        G.col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp > 0) {
            int u = st[--sp];
            for (int k = 0; k < G.deg[u]; k++) {
                int v = G.adj[u][k];
                if (G.col[v] == -1) {
                    G.col[v] = 1 - G.col[u];
                    st[sp++] = v;
                } else if (G.col[v] == G.col[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

static void make_kdd(void) {
    int k = d_;
    memset(G.deg, 0, sizeof(G.deg));
    G.n = 2 * k;
    for (int v = 0; v < 2 * k; v++) G.col[v] = (v < k) ? 0 : 1;
    for (int a = 0; a < k; a++)
        for (int b = 0; b < k; b++)
            add_edge(a, k + b);
}

static void write_out(void) {
    int m = 0;
    for (int v = 0; v < G.n; v++)
        for (int k = 0; k < G.deg[v]; k++)
            if (G.adj[v][k] > v) m++;
    printf("%d %d\n", G.n, m);
    for (int v = 0; v < G.n; v++)
        for (int k = 0; k < G.deg[v]; k++)
            if (G.adj[v][k] > v) printf("%d %d\n", v, G.adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    c0 = clock();
    w0 = time(NULL);
    if (d_ < 1 || d_ >= MAXD || D_ < 1) {
        printf("1 0\n");
        return 0;
    }

    int n = 0, m = 0, ok = 1;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n >= MAXN || m < 0) ok = 0;
    memset(G.deg, 0, sizeof(G.deg));
    G.n = ok ? n : 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (!ok) continue;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; continue; }
        if (G.deg[u] >= d_ || G.deg[v] >= d_ || has_edge(u, v)) { ok = 0; continue; }
        add_edge(u, v);
    }
    if (ok && !bipartite_colour()) ok = 0;
    if (!ok) make_kdd();

    if (D_ < 2) {
        write_out();
        return 0;
    }
    if (bad_pairs() != 0) {
        anneal(20000, T_HOT, T_COLD);
        if (bad_pairs() != 0) make_kdd();
    }

    save_state(&best_s);
    int best_n = G.n;
    while (!timeup()) {
        save_state(&snap_s);
        int r = rndint(100);
        int good;
        if (r < 55) good = op_add(800);
        else if (r < 85) good = op_kill_regrow();
        else good = op_shake();
        if (good) {
            if (G.n > best_n) {
                best_n = G.n;
                save_state(&best_s);
            }
            if (G.n < snap_s.n - 1 && rnd01() < 0.8) load_state(&snap_s);
        } else {
            load_state(&snap_s);
        }
        if (G.n < best_n - 3) load_state(&best_s);
    }
    load_state(&best_s);
    if (bad_pairs() != 0) make_kdd();
    write_out();
    return 0;
}
"""


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q small enough to build fast)."""
    for q in range(d - 1, 1, -1):
        if q <= 11 and lib.is_prime_power(q):
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=200):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
    if D < 2:
        return n, edges
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

    # Structured start: generalized quadrangle for D >= 4, projective plane for D = 3.
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng, attempts=30)
            consider(n1, e1)
            n2, e2 = _duplicate_twins(n1, e1, d, rng)
            e2 = _saturate_edges(n2, e2, d, rng)
            consider(n2, e2)

    # Calibration cases that already meet the Moore bound need no search.
    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # C engine: annealing repair, add-vertex, kill-regrow, plateau shakes.
    if D >= 2:
        elapsed = time.monotonic() - start
        budget = 0.9 * time_limit - elapsed - 1.5
        if budget >= 1.0:
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
