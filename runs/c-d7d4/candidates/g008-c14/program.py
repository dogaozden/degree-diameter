import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1400
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define ANN_ITERS 600

typedef uint64_t BRow[MAXW];

static int N, Dd, DIAM;
static int nb[MAXN][MAXD];
static int deg[MAXN];
static int col[MAXN];
static BRow BUF1[MAXN], BUF2[MAXN];
static uint64_t rs = 88172645463325252ULL;
static double budget_s;
static clock_t t0;

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int nb[MAXN][MAXD];
} Snap;

static Snap snapCur, snapBest;

typedef struct { int a, bi, b, c, ei, e; } Sw;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) / 9007199254740992.0; }

static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }

static int pc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has(int v, int u) {
    for (int k = 0; k < deg[v]; k++)
        if (nb[v][k] == u) return 1;
    return 0;
}

static void repl(int v, int from, int to) {
    for (int k = 0; k < deg[v]; k++)
        if (nb[v][k] == from) { nb[v][k] = to; return; }
}

static void shuffle(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static BRow *balls(int r) {
    BRow *cur = BUF1, *nxt = BUF2;
    int w = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        memset(cur[v], 0, sizeof(BRow));
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < N; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * w);
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[nb[v][k]];
                for (int i = 0; i < w; i++) nxt[v][i] |= src[i];
            }
        }
        BRow *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

static long cost(void) {
    BRow *b = balls(DIAM);
    int w = (N + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int i = 0; i < w; i++) c += pc(b[v][i]);
        bad += N - c;
    }
    return bad / 2;
}

static int side_list(int *s0, int color) {
    int n0 = 0;
    for (int v = 0; v < N; v++)
        if (col[v] == color) s0[n0++] = v;
    return n0;
}

/* Propose a bipartite double-edge switch: a-b, c-e -> a-e, c-b (a, c on side 0). */
static int propose(const int *s0, int n0, Sw *w) {
    if (n0 < 2) return 0;
    for (int t = 0; t < 40; t++) {
        int a = s0[rndint(n0)];
        if (deg[a] == 0) continue;
        int bi = rndint(deg[a]);
        int b = nb[a][bi];
        int c = s0[rndint(n0)];
        if (c == a || deg[c] == 0) continue;
        int ei = rndint(deg[c]);
        int e = nb[c][ei];
        if (has(a, e) || has(c, b)) continue;
        w->a = a; w->bi = bi; w->b = b; w->c = c; w->ei = ei; w->e = e;
        return 1;
    }
    return 0;
}

static void apply_sw(const Sw *w) {
    nb[w->a][w->bi] = w->e;
    repl(w->b, w->a, w->c);
    nb[w->c][w->ei] = w->b;
    repl(w->e, w->c, w->a);
}

static void undo_sw(const Sw *w) {
    nb[w->a][w->bi] = w->b;
    repl(w->b, w->c, w->a);
    nb[w->c][w->ei] = w->e;
    repl(w->e, w->a, w->c);
}

/* Degree-preserving switches that keep the diameter bound (zero-cost plateau walk). */
static void plateau(int steps) {
    static int s0[MAXN];
    int n0 = side_list(s0, 0);
    Sw w;
    for (int i = 0; i < steps; i++) {
        if (!propose(s0, n0, &w)) continue;
        apply_sw(&w);
        if (cost() != 0) undo_sw(&w);
    }
}

/* Switch-based annealing on the number of bad pairs. Returns 1 if cost reaches 0. */
static int anneal(int iters) {
    static int s0[MAXN];
    int n0 = side_list(s0, 0);
    long cur = cost();
    Sw w;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && elapsed() > budget_s) break;
        if (!propose(s0, n0, &w)) continue;
        apply_sw(&w);
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rnd01() < 0.03)) cur = nw;
        else undo_sw(&w);
    }
    return cur == 0;
}

/* Add cross-side edges between deficient vertices (never increases distances). */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] >= Dd) continue;
        if (col[v] == 0) L0[n0++] = v;
        else L1[n1++] = v;
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg[a] < Dd; j++) {
            int b = L1[j];
            if (deg[b] >= Dd || has(a, b)) continue;
            nb[a][deg[a]++] = b;
            nb[b][deg[b]++] = a;
        }
    }
}

/* Add a vertex of colour `side` whose neighbours greedily cover the (D-1)-balls. */
static int add_vertex(int side) {
    if (N + 1 >= MAXN) return 0;
    int w = (N + 63) >> 6;
    BRow *B = balls(DIAM - 1);
    BRow cov;
    memset(cov, 0, sizeof(BRow));
    static int mark[MAXN];
    static int stamp = 0;
    stamp++;
    int chosen[MAXD];
    int nc = 0;
    for (int step = 0; step < Dd; step++) {
        int best = -1, bestg = 0;
        long bestsc = -(1L << 40);
        for (int s = 0; s < N; s++) {
            if (col[s] != 1 - side || mark[s] == stamp) continue;
            int g = 0;
            for (int i = 0; i < w; i++) g += pc(B[s][i] & ~cov[i]);
            long sc = (long)g * 16 + rndint(16) - (deg[s] >= Dd ? 1000 : 0);
            if (sc > bestsc) { bestsc = sc; best = s; bestg = g; }
        }
        if (best < 0 || bestg == 0) break;
        mark[best] = stamp;
        chosen[nc++] = best;
        for (int i = 0; i < w; i++) cov[i] |= B[best][i];
    }
    if (nc == 0) return 0;
    int v = N++;
    col[v] = side;
    deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= Dd) {
            int idx = rndint(deg[s]);
            int t = nb[s][idx];
            nb[s][idx] = v;
            for (int j = 0; j < deg[t]; j++) {
                if (nb[t][j] == s) {
                    nb[t][j] = nb[t][deg[t] - 1];
                    deg[t]--;
                    break;
                }
            }
        } else {
            nb[s][deg[s]++] = v;
        }
        nb[v][deg[v]++] = s;
    }
    return 1;
}

static void save(Snap *s) {
    s->n = N;
    memcpy(s->deg, deg, sizeof(int) * N);
    memcpy(s->col, col, sizeof(int) * N);
    memcpy(s->nb, nb, sizeof(nb[0]) * N);
}

static void restore(const Snap *s) {
    N = s->n;
    memcpy(deg, s->deg, sizeof(int) * N);
    memcpy(col, s->col, sizeof(int) * N);
    memcpy(nb, s->nb, sizeof(nb[0]) * N);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    budget_s = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    Dd = d;
    DIAM = D;
    int ok = (n >= 1 && n <= MAXN - 200 && m >= 0 && d >= 1 && d <= MAXD && D >= 2);
    if (ok) {
        N = n;
        for (int v = 0; v < N; v++) deg[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
            if (deg[u] >= d || deg[v] >= d || has(u, v)) { ok = 0; break; }
            nb[u][deg[u]++] = v;
            nb[v][deg[v]++] = u;
        }
    }
    if (ok) {
        static int q[MAXN];
        for (int v = 0; v < N; v++) col[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int x = nb[u][k];
                    if (col[x] < 0) { col[x] = 1 - col[u]; q[qt++] = x; }
                    else if (col[x] == col[u]) { ok = 0; break; }
                }
            }
        }
    }

    t0 = clock();
    if (!ok) { printf("0 0\n"); return 0; }
    if (cost() != 0) anneal(20000);
    if (cost() != 0) { printf("0 0\n"); return 0; }

    save(&snapBest);
    int bestN = N;

    while (elapsed() < budget_s && N + 2 < MAXN) {
        plateau(12);
        save(&snapCur);
        int side = rndint(2);
        int grown = 0;
        if (add_vertex(side)) {
            fill();
            if (anneal(ANN_ITERS)) grown = 1;
        }
        if (grown) {
            save(&snapCur);
            if (N > bestN) {
                bestN = N;
                save(&snapBest);
            }
        } else {
            restore(&snapCur);
        }
    }

    const Snap *b = &snapBest;
    int m2 = 0;
    for (int v = 0; v < b->n; v++)
        for (int k = 0; k < b->deg[v]; k++)
            if (b->nb[v][k] > v) m2++;
    printf("%d %d\n", b->n, m2);
    for (int v = 0; v < b->n; v++)
        for (int k = 0; k < b->deg[v]; k++)
            if (b->nb[v][k] > v) printf("%d %d\n", v, b->nb[v][k]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q) (diameter 4)."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python-side growth helpers (cover vertices, saturation, twins).
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
    """Greedily add vertices whose neighbourhoods cover the (D-1)-balls of the whole graph."""
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
    """Join deficient opposite-side vertices in random order (never increases distances)."""
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
    """Extend by cover vertices, then saturate with the remaining spare degree."""
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
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
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
    """One randomized pipeline mixing twin duplication with cover growth."""
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
# Build: structured base and Python growth, then the C search engine.
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
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and n <= moore and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

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
            n1, e1 = _grow(n0, e0, d, D, start + 0.12 * time_limit, rng)
            consider(n1, e1)

    # Randomized twin/cover pipelines from the structured base.
    if D >= 2 and best_n < moore:
        trial_end = start + 0.22 * time_limit
        while time.monotonic() < trial_end and best_n < moore:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C engine: switch-based repair plus add-vertex growth from the best valid graph.
    if D >= 2 and best_n < moore:
        remaining = start + 0.85 * time_limit - time.monotonic() - 2.0
        if remaining > 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(remaining, 2)],
                                stdin_graph=(best_n, best_e), timeout=remaining + 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
