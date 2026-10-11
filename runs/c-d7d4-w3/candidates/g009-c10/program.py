import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine (new this round).
#
# Works on a fixed bipartite graph with max degree d. The state is kept as
# bitset balls of radius D, and the cost is the number of vertex pairs at
# distance > D. Moves:
#   swap    double-edge swap (a-b, c-e) -> (a-e, c-b), keeps all degrees
#   add     join two spare-degree vertices on opposite sides
#   rewire  move one endpoint of an edge to a spare vertex on that side
# Simulated annealing accepts moves on cost. When cost hits 0, the graph is
# saved and grown by one vertex, chosen by greedy set cover of radius-(D-1)
# balls. Stalls restart from the best saved graph with random perturbation.
# Every saved graph has cost 0, degree <= d, and is bipartite.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 4096
#define WCAP (NCAP / 64)
#define MAXD 32

typedef uint64_t Row[WCAP];

static int d_, D_, n_;
static int color_[NCAP];
static int deg_[NCAP];
static int adj_[NCAP][MAXD];

static Row BC[NCAP];
static Row SCR[NCAP];
static Row CB[NCAP];

static int best_n = -1;
static int best_valid = 0;
static int best_color[NCAP];
static int best_deg[NCAP];
static int best_adj[NCAP][MAXD];

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int m) {
    if (m <= 0) return 0;
    return (int)(rnd() % (uint64_t)m);
}

static double rndu(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg_[a]; k++)
        if (adj_[a][k] == b) return 1;
    return 0;
}

static void add_nb(int v, int x) {
    adj_[v][deg_[v]++] = x;
}

static void rm_nb(int v, int x) {
    for (int k = 0; k < deg_[v]; k++)
        if (adj_[v][k] == x) {
            adj_[v][k] = adj_[v][--deg_[v]];
            return;
        }
}

static void repl_nb(int v, int old, int nw) {
    for (int k = 0; k < deg_[v]; k++)
        if (adj_[v][k] == old) {
            adj_[v][k] = nw;
            return;
        }
}

/* dst[v] = bitset of vertices within distance r of v */
static void compute_balls(int r, Row *dst) {
    int W = (n_ + 63) >> 6;
    Row *X = SCR, *Y = dst;
    for (int v = 0; v < n_; v++) {
        for (int w = 0; w < W; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n_; v++) {
            for (int w = 0; w < W; w++) Y[v][w] = X[v][w];
            for (int k = 0; k < deg_[v]; k++) {
                const uint64_t *src = X[adj_[v][k]];
                for (int w = 0; w < W; w++) Y[v][w] |= src[w];
            }
        }
        Row *t = X;
        X = Y;
        Y = t;
    }
    if (X != dst) {
        for (int v = 0; v < n_; v++)
            for (int w = 0; w < W; w++) dst[v][w] = X[v][w];
    }
}

static long cost_full(void) {
    int W = (n_ + 63) >> 6;
    compute_balls(D_, CB);
    long bad = 0;
    for (int v = 0; v < n_; v++) {
        int p = 0;
        for (int w = 0; w < W; w++) p += pop64(CB[v][w]);
        bad += n_ - p;
    }
    return bad / 2;
}

static void save_best(int valid) {
    best_n = n_;
    best_valid = valid;
    memcpy(best_color, color_, sizeof(int) * (size_t)n_);
    memcpy(best_deg, deg_, sizeof(int) * (size_t)n_);
    memcpy(best_adj, adj_, sizeof(adj_[0]) * (size_t)n_);
}

static void load_best(void) {
    n_ = best_n;
    memcpy(color_, best_color, sizeof(int) * (size_t)n_);
    memcpy(deg_, best_deg, sizeof(int) * (size_t)n_);
    memcpy(adj_, best_adj, sizeof(adj_[0]) * (size_t)n_);
}

static void print_best(void) {
    int n = best_n < 0 ? 0 : best_n;
    long m = 0;
    for (int v = 0; v < n; v++)
        for (int k = 0; k < best_deg[v]; k++)
            if (best_adj[v][k] > v) m++;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < best_deg[v]; k++) {
            int u = best_adj[v][k];
            if (u > v) printf("%d %d\n", v, u);
        }
}

static void shuffle_ints(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add one vertex on the side that has candidates, joined greedily to
   spare-degree vertices on the other side so as to cover radius-D-1 balls. */
static int grow_vertex(void) {
    if (n_ + 1 >= NCAP) return 0;
    int W = (n_ + 63) >> 6;
    int c = rndi(2);
    int cand[NCAP];
    int nc = 0;
    for (int t = 0; t < 2; t++) {
        nc = 0;
        for (int v = 0; v < n_; v++)
            if (color_[v] == 1 - c && deg_[v] < d_) cand[nc++] = v;
        if (nc > 0) break;
        c = 1 - c;
    }
    int v = n_;
    color_[v] = c;
    deg_[v] = 0;
    int chosen[MAXD];
    int nch = 0;
    if (nc > 0) {
        compute_balls(D_ - 1, BC);
        shuffle_ints(cand, nc);
        Row cov;
        for (int w = 0; w < W; w++) cov[w] = 0;
        while (nch < d_ && nc > 0) {
            int bi = -1, bg = 0;
            for (int i = 0; i < nc; i++) {
                int g = 0;
                for (int w = 0; w < W; w++) g += pop64(BC[cand[i]][w] & ~cov[w]);
                if (g > bg) {
                    bg = g;
                    bi = i;
                }
            }
            if (bi < 0) break;
            int s = cand[bi];
            cand[bi] = cand[--nc];
            chosen[nch++] = s;
            for (int w = 0; w < W; w++) cov[w] |= BC[s][w];
        }
    }
    for (int i = 0; i < nch; i++) {
        add_nb(v, chosen[i]);
        add_nb(chosen[i], v);
    }
    n_++;
    return 1;
}

/* Random double-edge swap candidates: a,c on side 0; b,e on side 1. */
static int pick_swap(int *pa, int *pb, int *pc, int *pe) {
    for (int t = 0; t < 200; t++) {
        int a = rndi(n_);
        if (color_[a] != 0 || deg_[a] == 0) continue;
        int b = adj_[a][rndi(deg_[a])];
        int c = rndi(n_);
        if (c == a || color_[c] != 0 || deg_[c] == 0) continue;
        int e = adj_[c][rndi(deg_[c])];
        if (e == b) continue;
        if (has_edge(a, e) || has_edge(c, b)) continue;
        *pa = a;
        *pb = b;
        *pc = c;
        *pe = e;
        return 1;
    }
    return 0;
}

static void apply_swap(int a, int b, int c, int e) {
    repl_nb(a, b, e);
    repl_nb(c, e, b);
    repl_nb(b, a, c);
    repl_nb(e, c, a);
}

static void undo_swap(int a, int b, int c, int e) {
    repl_nb(a, e, b);
    repl_nb(c, b, e);
    repl_nb(b, c, a);
    repl_nb(e, a, c);
}

static void try_swap(long *cur, double T) {
    int a, b, c, e;
    if (!pick_swap(&a, &b, &c, &e)) return;
    apply_swap(a, b, c, e);
    long nc = cost_full();
    if (nc <= *cur || rndu() < exp(-(double)(nc - *cur) / T)) *cur = nc;
    else undo_swap(a, b, c, e);
}

/* Returns -1 if no move was possible, 0 if rejected, 1 if accepted. */
static int try_add(long *cur, double T) {
    int sp0[NCAP], sp1[NCAP];
    int n0 = 0, n1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg_[v] >= d_) continue;
        if (color_[v] == 0) sp0[n0++] = v;
        else sp1[n1++] = v;
    }
    if (n0 == 0 || n1 == 0) return -1;
    for (int t = 0; t < 50; t++) {
        int a = sp0[rndi(n0)], b = sp1[rndi(n1)];
        if (has_edge(a, b)) continue;
        add_nb(a, b);
        add_nb(b, a);
        long nc = cost_full();
        if (nc <= *cur || rndu() < exp(-(double)(nc - *cur) / T)) {
            *cur = nc;
            return 1;
        }
        rm_nb(a, b);
        rm_nb(b, a);
        return 0;
    }
    return -1;
}

/* Move edge (x,y) to (x,z), where z is a spare vertex on y's side. */
static int try_rewire(long *cur, double T) {
    int sp[NCAP];
    int ns = 0;
    for (int v = 0; v < n_; v++)
        if (deg_[v] < d_) sp[ns++] = v;
    if (ns == 0) return -1;
    for (int t = 0; t < 60; t++) {
        int x = rndi(n_);
        if (deg_[x] == 0) continue;
        int y = adj_[x][rndi(deg_[x])];
        int z = sp[rndi(ns)];
        if (z == y || z == x || color_[z] != color_[y] || has_edge(x, z)) continue;
        repl_nb(x, y, z);
        rm_nb(y, x);
        add_nb(z, x);
        long nc = cost_full();
        if (nc <= *cur || rndu() < exp(-(double)(nc - *cur) / T)) {
            *cur = nc;
            return 1;
        }
        rm_nb(z, x);
        add_nb(y, x);
        repl_nb(x, z, y);
        return 0;
    }
    return -1;
}

static void perturb(int k) {
    for (int i = 0; i < k; i++) {
        int a, b, c, e;
        if (pick_swap(&a, &b, &c, &e)) apply_swap(a, b, c, e);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    rs ^= 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 1;
    double limit = atof(argv[4]);
    clock_t t0 = clock();

    int n, m;
    if (scanf("%d %d", &n, &m) != 2) {
        printf("0 0\n");
        return 0;
    }
    if (n < 0 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) {
            m = i;
            break;
        }
    }

    int ok = (n <= NCAP - 4 && d_ >= 1 && d_ <= MAXD && D_ >= 2);
    if (ok) {
        n_ = n;
        for (int v = 0; v < n; v++) deg_[v] = 0;
        for (int i = 0; i < m && ok; i++) {
            int u = eu[i], v = ev[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v ||
                deg_[u] >= d_ || deg_[v] >= d_ || has_edge(u, v)) {
                ok = 0;
            } else {
                add_nb(u, v);
                add_nb(v, u);
            }
        }
    }
    if (ok) {
        static int queue[NCAP];
        for (int v = 0; v < n; v++) color_[v] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (color_[s] != -1) continue;
            color_[s] = 0;
            int qh = 0, qt = 0;
            queue[qt++] = s;
            while (qh < qt && ok) {
                int u = queue[qh++];
                for (int k = 0; k < deg_[u] && ok; k++) {
                    int v = adj_[u][k];
                    if (color_[v] == -1) {
                        color_[v] = 1 - color_[u];
                        queue[qt++] = v;
                    } else if (color_[v] == color_[u]) {
                        ok = 0;
                    }
                }
            }
        }
    }
    if (!ok) {
        printf("%d %d\n", n, m);
        for (int i = 0; i < m; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }
    free(eu);
    free(ev);

    long cur = cost_full();
    save_best(cur == 0);
    long minc = cur, since = 0;
    double T = 1.0;
    const long STALL = 20000;

    while ((double)(clock() - t0) / CLOCKS_PER_SEC < limit) {
        if (cur == 0) {
            if (!best_valid || n_ > best_n) save_best(1);
            if (!grow_vertex()) break;
            cur = cost_full();
            minc = cur;
            since = 0;
            T = 1.0;
            continue;
        }
        double u = rndu();
        int r = -1;
        if (u < 0.2) r = try_add(&cur, T);
        else if (u < 0.4) r = try_rewire(&cur, T);
        if (r < 0) try_swap(&cur, T);

        if (cur < minc) {
            minc = cur;
            since = 0;
        } else {
            since++;
        }
        T *= 0.99995;
        if (T < 0.12) T = 0.12;
        if (since > STALL) {
            if (best_valid) {
                load_best();
                perturb(30);
            }
            cur = cost_full();
            minc = cur;
            since = 0;
            T = 1.0;
        }
    }
    print_best();
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
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


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


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
# Bipartite voltage lifts over small groups (Python phase).
# ----------------------------------------------------------------------------

def _group_options(G):
    """(M, k, r) triples describing groups of order G: cyclic plus Z_M x|_r Z_k with M*k = G."""
    opts = [(G, 1, 1)]
    for k in range(2, G + 1):
        if G % k:
            continue
        M = G // k
        if M < 2:
            continue
        for r in range(1, M):
            if math.gcd(r, M) == 1 and pow(r, k, M) == 1 % M:
                opts.append((M, k, r))
    return opts


def _random_darts(s, d, G, rng):
    a = [i for i in range(s) for _ in range(d)]
    b = list(a)
    rng.shuffle(b)
    return [(i, s + j, rng.randrange(G)) for i, j in zip(a, b)]


def _lift_search(d, D, s, G, mul, rng, deadline, darts=None, temp=0.6):
    if darts is None:
        darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    while cur > 0:
        if time.monotonic() > deadline:
            return None, darts, temp
        old = list(darts)
        k = len(darts)
        if k >= 2 and rng.random() < 0.5:
            p = rng.randrange(k)
            q = rng.randrange(k)
            if p == q:
                continue
            ip, jp, gp = darts[p]
            iq, jq, gq = darts[q]
            darts[p] = (ip, jq, gp)
            darts[q] = (iq, jp, gq)
        else:
            p = rng.randrange(k)
            i, j, _ = darts[p]
            darts[p] = (i, j, rng.randrange(G))
        n2, e2 = lib.group_lift(2 * s, darts, G, mul)
        new = _cost(_to_sets(n2, e2), D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            n, e = n2, e2
        else:
            darts = old
        temp = max(0.05, temp * 0.999)
    return (n, e), darts, temp


def _lift_phase(d, D, get_best, deadline, rng, consider):
    states = {}
    while time.monotonic() < deadline:
        best_n = get_best()
        states = {key: v for key, v in states.items() if 2 * key[0] * key[1] > best_n}
        if states and rng.random() < 0.7:
            key = rng.choice(list(states))
            darts, temp = states.pop(key)
            s, G, M, k, r = key
        else:
            darts, temp = None, 0.6
            s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
            G_min = best_n // (2 * s) + 1
            G = G_min + rng.randrange(4)
            opts = _group_options(G)
            if not opts:
                continue
            M, k, r = rng.choice(opts)
            key = (s, G, M, k, r)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res, darts, temp = _lift_search(d, D, s, G, mul, rng, slice_end, darts, temp)
        if res is None:
            states[key] = (darts, temp)
            if len(states) > 40:
                states.pop(next(iter(states)))
            continue
        n, e = res
        consider(n, e)
        n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
        consider(n2, e2)


# ----------------------------------------------------------------------------
# C engine driver.
# ----------------------------------------------------------------------------

def _c_phase(d, D, seed, n, e, budget):
    """Run the C annealer for `budget` CPU seconds from graph (n, e); return (n, e) or None."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, e), timeout=budget + 6.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver. Python builds structured bases and lifts for the first part of the
# budget; the C annealer then works from the best graph for the rest.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    def at(f):
        return start + f * time_limit

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    if base is not None:
        consider(base[0], base[1])
        n1, e1 = _grow(base[0], base[1], d, D, at(0.08), rng)
        consider(n1, e1)
    if D >= 2:
        trial_end = at(0.12)
        base_n, base_e = best_n, list(best_e)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.25):
        _lift_phase(d, D, lambda: best_n, at(0.25), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C annealer from the best valid graph, using the remaining budget.
    if D >= 2:
        c_end = start + 0.88 * time_limit - 1.5
        c_budget = c_end - time.monotonic()
        if c_budget > 1.0:
            try:
                n, e = _c_phase(d, D, seed, best_n, best_e, c_budget)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
