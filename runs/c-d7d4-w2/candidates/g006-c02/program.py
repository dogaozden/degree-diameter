import itertools
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree is q + 1, diameter is 4, order is 2(q+1)(q^2+1).
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python-side helpers: cover growth, saturation, twin duplication.
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
    """Greedily add vertices whose neighbourhoods are cover sets of the other side."""
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


# ----------------------------------------------------------------------------
# C engine: bitset-based plateau walk with cost-driven vertex insertion.
#
# State: a bipartite graph with max degree d and diameter <= D, kept valid at
# all times. Cost = number of vertex pairs at distance > D (computed with
# bitset balls). Moves:
#   * plateau: degree-preserving bipartite double-edge switches, accepted only
#     when the state stays valid;
#   * growth: add a vertex joined to a greedy cover of the other side (one
#     neighbour loses an edge if it is saturated), add cross edges, then
#     anneal with switches at falling temperature. Accept only if cost 0.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)

typedef uint64_t u64;

static int d_, D_, n_;
static int deg_[MAXN];
static int col_[MAXN];
static int adj_[MAXN][MAXD];
static u64 ballA[MAXN * MAXW];
static u64 ballR[MAXN * MAXW];
static u64 ballT[MAXN * MAXW];

typedef struct {
    int n;
    int deg[MAXN];
    int col[MAXN];
    int adj[MAXN][MAXD];
} Snap;

static Snap snapBase, snapBest;
static double limit_;
static clock_t t0_;
static u64 rs_ = 88172645463325252ULL;

static u64 rnd64(void) {
    rs_ ^= rs_ << 13;
    rs_ ^= rs_ >> 7;
    rs_ ^= rs_ << 17;
    return rs_;
}
static int rndi(int k) { return (int)(rnd64() % (u64)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) {
    return (double)(clock() - t0_) / CLOCKS_PER_SEC >= limit_;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg_[u]; i++)
        if (adj_[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj_[u][deg_[u]++] = v;
    adj_[v][deg_[v]++] = u;
}

static void rm_half(int u, int v) {
    for (int i = 0; i < deg_[u]; i++) {
        if (adj_[u][i] == v) {
            adj_[u][i] = adj_[u][--deg_[u]];
            return;
        }
    }
}

static void del_edge(int u, int v) {
    rm_half(u, v);
    rm_half(v, u);
}

/* out[v] = bitmask of vertices within distance r of v. */
static void balls(int r, u64 *out) {
    int n = n_;
    int W = (n + 63) >> 6;
    memset(out, 0, sizeof(u64) * (size_t)n * W);
    for (int v = 0; v < n; v++)
        out[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int k = 0; k < r; k++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = ballT + (size_t)v * W;
            memcpy(dst, out + (size_t)v * W, sizeof(u64) * W);
            for (int i = 0; i < deg_[v]; i++) {
                const u64 *src = out + (size_t)adj_[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= src[w];
            }
        }
        memcpy(out, ballT, sizeof(u64) * (size_t)n * W);
    }
}

/* Number of unordered pairs at distance > D_ (unreachable pairs count). */
static long cost(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    balls(D_, ballA);
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++)
            c += __builtin_popcountll(ballA[(size_t)v * W + w]);
        bad += n - c;
    }
    return bad / 2;
}

static void save_snap(Snap *s) {
    s->n = n_;
    memcpy(s->deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(s->col, col_, sizeof(int) * (size_t)n_);
    memcpy(s->adj, adj_, sizeof(int) * MAXD * (size_t)n_);
}

static void load_snap(const Snap *s) {
    n_ = s->n;
    memcpy(deg_, s->deg, sizeof(int) * (size_t)n_);
    memcpy(col_, s->col, sizeof(int) * (size_t)n_);
    memcpy(adj_, s->adj, sizeof(int) * MAXD * (size_t)n_);
}

/* Random vertex on side s with positive degree, or -1. */
static int pick_side(int s) {
    for (int t = 0; t < 200; t++) {
        int v = rndi(n_);
        if (col_[v] == s && deg_[v] > 0) return v;
    }
    return -1;
}

/* Propose a switch a-b, c-e -> a-e, c-b with a, c on side 0. */
static int propose(int *pa, int *pb, int *pc, int *pe) {
    int a = pick_side(0);
    int c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj_[a][rndi(deg_[a])];
    int e = adj_[c][rndi(deg_[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}

static void apply_switch(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Plateau walk: accept only switches that keep the state valid (cost 0). */
static void plateau(int steps) {
    for (int i = 0; i < steps && !timeup(); i++) {
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        if (cost() != 0) undo_switch(a, b, c, e);
    }
}

/* Simulated annealing on switches. Returns the cost of the final state. */
static long anneal(int iters, double T0, double T1) {
    long cur = cost();
    for (int it = 0; it < iters && cur > 0 && !timeup(); it++) {
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        apply_switch(a, b, c, e);
        long nw = cost();
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            undo_switch(a, b, c, e);
        }
    }
    return cur;
}

static void shuffle(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Add cross-side edges between deficient vertices (only shortens distances). */
static void fill(void) {
    static int L0[MAXN], L1[MAXN];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] < d_) {
            if (col_[v] == 0) L0[n0++] = v;
            else L1[n1++] = v;
        }
    }
    shuffle(L0, n0);
    shuffle(L1, n1);
    for (int i = 0; i < n0; i++) {
        int a = L0[i];
        for (int j = 0; j < n1 && deg_[a] < d_; j++) {
            int b = L1[j];
            if (deg_[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Append a vertex on the side opposite to a greedy cover of side s. */
static void grow_vertex(void) {
    int n = n_;
    int W = (n + 63) >> 6;
    balls(D_ - 1, ballR);
    int s = rndi(2);
    static int cand[MAXN];
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col_[v] == s) cand[nc++] = v;

    u64 covered[MAXW];
    memset(covered, 0, sizeof(u64) * (size_t)W);
    char used[MAXN];
    memset(used, 0, (size_t)n);
    int chosen[MAXD];
    int nch = 0;

    for (int k = 0; k < d_; k++) {
        long bestkey = -1;
        int bv = -1;
        for (int i = 0; i < nc; i++) {
            int c = cand[i];
            if (used[c]) continue;
            long g = 0;
            for (int w = 0; w < W; w++)
                g += __builtin_popcountll(ballR[(size_t)c * W + w] & ~covered[w]);
            if (g == 0) continue;
            long key = g * 16 + rndi(16);
            if (key > bestkey) {
                bestkey = key;
                bv = c;
            }
        }
        if (bv < 0) break;
        used[bv] = 1;
        chosen[nch++] = bv;
        for (int w = 0; w < W; w++)
            covered[w] |= ballR[(size_t)bv * W + w];
    }
    if (nch == 0) return;

    int v = n_;
    n_++;
    deg_[v] = 0;
    col_[v] = 1 - s;
    for (int i = 0; i < nch; i++) {
        int c = chosen[i];
        if (deg_[c] >= d_) {
            int t = adj_[c][rndi(deg_[c])];
            del_edge(c, t);
        }
        add_edge(c, v);
    }
}

static void print_snap(const Snap *s) {
    long m = 0;
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++)
            if (u < s->adj[u][i]) m++;
    printf("%d %ld\n", s->n, m);
    for (int u = 0; u < s->n; u++)
        for (int i = 0; i < s->deg[u]; i++)
            if (u < s->adj[u][i]) printf("%d %d\n", u, s->adj[u][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    u64 seed = (u64)strtoull(argv[3], NULL, 10);
    limit_ = atof(argv[4]);
    rs_ ^= (seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (rs_ == 0) rs_ = 1;
    for (int i = 0; i < 16; i++) rnd64();
    t0_ = clock();

    int n_in = 1, m_in = 0;
    if (scanf("%d %d", &n_in, &m_in) != 2) {
        n_in = 1;
        m_in = 0;
    }
    if (m_in < 0) m_in = 0;
    int *eu = malloc(sizeof(int) * (size_t)(m_in + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m_in + 1));
    int ok = 1;
    for (int i = 0; i < m_in; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            ok = 0;
            m_in = i;
            break;
        }
    }
    if (n_in < 1 || n_in > MAXN - 256 || d_ < 1 || d_ >= MAXD - 1 || D_ < 2) ok = 0;

    if (ok) {
        n_ = n_in;
        for (int v = 0; v < n_; v++) deg_[v] = 0;
        for (int i = 0; i < m_in && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n_ || v >= n_ || u == v) {
                ok = 0;
                break;
            }
            if (deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
    }

    if (ok) {
        static int st[MAXN];
        for (int v = 0; v < n_; v++) col_[v] = -1;
        for (int s = 0; s < n_ && ok; s++) {
            if (col_[s] != -1) continue;
            int sp = 0;
            col_[s] = 0;
            st[sp++] = s;
            while (sp > 0 && ok) {
                int u = st[--sp];
                for (int i = 0; i < deg_[u]; i++) {
                    int v = adj_[u][i];
                    if (col_[v] == -1) {
                        col_[v] = 1 - col_[u];
                        st[sp++] = v;
                    } else if (col_[v] == col_[u]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }

    if (ok) {
        long c0 = cost();
        if (c0 > 0) c0 = anneal(20000, 0.8, 0.05);
        if (c0 != 0) ok = 0;
    }

    if (ok) {
        save_snap(&snapBest);
        save_snap(&snapBase);
        while (!timeup()) {
            plateau(300);
            save_snap(&snapBase);
            int nb = n_;
            grow_vertex();
            fill();
            long c = anneal(1500, 0.6, 0.03);
            if (c != 0) {
                load_snap(&snapBase);
            } else if (n_ > nb) {
                save_snap(&snapBest);
            }
        }
        print_snap(&snapBest);
    } else {
        printf("%d %d\n", n_in, m_in);
        for (int i = 0; i < m_in; i++) printf("%d %d\n", eu[i], ev[i]);
    }

    free(eu);
    free(ev);
    return 0;
}
"""


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

    # Structured base: W(q) for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        consider(base[0], base[1])

    # Python pre-stage: cover growth and twin duplication from the best base.
    if D >= 2:
        pre_end = start + 0.25 * time_limit
        n1, e1 = _grow(best_n, list(best_e), d, D, pre_end, rng)
        consider(n1, e1)
        n2, e2 = _duplicate_twins(best_n, list(best_e), d, rng)
        e2 = _saturate_edges(n2, e2, d, rng)
        consider(n2, e2)

    # C engine: plateau walk and annealed vertex insertion from the best graph.
    elapsed = time.monotonic() - start
    budget = 0.88 * time_limit - elapsed - 2.0
    if D >= 2 and budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=(best_n, list(best_e)),
                             timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
