import itertools
import math
import random
import time

import lib

# Phases A, B, R and L are Python constructions and searches. Phase C runs
# a C annealing engine (C_SOURCE) on the best valid graph. The engine grows
# the graph by two vertices at a time, repairs the diameter with edge
# switches that keep bipartiteness and degree, and keeps only valid graphs.
# If the C engine fails, the Python LNS runs in its place.


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define ITERS 3000

static int d_, D_, CAP, WC, n_, bn;
static int *adj, *deg, *col, *badj, *bdeg;
static uint64_t *R, *Q;
static uint64_t rs = 88172645463325252ULL;
static double deadline_s;

static uint64_t xs(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rnd(int m) { return (int)(xs() % (uint64_t)m); }
static double rndu(void) { return (double)(xs() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int isadj(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a * d_ + k] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    for (int k = 0; k < deg[v]; k++) {
        if (adj[v * d_ + k] == old) { adj[v * d_ + k] = nw; return; }
    }
}

static void add_edge(int x, int y) {
    adj[x * d_ + deg[x]++] = y;
    adj[y * d_ + deg[y]++] = x;
}

static void del_edge(int x, int y) {
    for (int k = 0; k < deg[x]; k++) {
        if (adj[x * d_ + k] == y) { adj[x * d_ + k] = adj[x * d_ + deg[x] - 1]; deg[x]--; break; }
    }
    for (int k = 0; k < deg[y]; k++) {
        if (adj[y * d_ + k] == x) { adj[y * d_ + k] = adj[y * d_ + deg[y] - 1]; deg[y]--; break; }
    }
}

/* Switch a-b and c-e (a,c on side 0; b,e on side 1) into a-e and c-b.
   Applying sw again with the same slots reverts the move. */
static void sw(int a, int i, int c, int j) {
    int b = adj[a * d_ + i], e = adj[c * d_ + j];
    adj[a * d_ + i] = e;
    adj[c * d_ + j] = b;
    repl(b, a, c);
    repl(e, c, a);
}

/* Number of unordered vertex pairs at distance more than D_. */
static long cost(void) {
    int n = n_, W = (n + 63) >> 6;
    uint64_t *cur = R, *nx = Q;
    for (int v = 0; v < n; v++) {
        uint64_t *s = cur + (size_t)v * WC;
        for (int w = 0; w < W; w++) s[w] = 0;
        s[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D_; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nx + (size_t)v * WC, *s = cur + (size_t)v * WC;
            for (int w = 0; w < W; w++) o[w] = s[w];
            for (int k = 0; k < deg[v]; k++) {
                uint64_t *t = cur + (size_t)adj[v * d_ + k] * WC;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cur; cur = nx; nx = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *s = cur + (size_t)v * WC;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(s[w]);
        bad += n - c;
    }
    return bad / 2;
}

/* Add every opposite-side pair of deficient vertices that is still free.
   Adding edges never increases distances, so this never raises the cost. */
static void fill(void) {
    int *L0 = malloc(sizeof(int) * (size_t)(n_ + 1));
    int *L1 = malloc(sizeof(int) * (size_t)(n_ + 1));
    int c0 = 0, c1 = 0;
    for (int v = 0; v < n_; v++) {
        if (deg[v] < d_) {
            if (col[v] == 0) L0[c0++] = v; else L1[c1++] = v;
        }
    }
    if (c0 > 0 && c1 > 0) {
        long trials = 20L * (c0 + c1);
        for (long t = 0; t < trials; t++) {
            int x = L0[rnd(c0)], y = L1[rnd(c1)];
            if (deg[x] >= d_ || deg[y] >= d_ || isadj(x, y)) continue;
            add_edge(x, y);
        }
    }
    free(L0);
    free(L1);
}

/* Remove up to d_ disjoint edges and replace them by two new vertices a (side 0)
   and b (side 1): a takes the side-1 ends, b takes the side-0 ends. Degrees are kept. */
static int grow(void) {
    int xs_[64], ys_[64], cnt = 0, tries = 0;
    int want = d_ < 64 ? d_ : 64;
    if (n_ + 2 > CAP) return 0;
    while (cnt < want && tries < 400) {
        tries++;
        int x;
        do { x = rnd(n_); } while (col[x] != 0 || deg[x] == 0);
        int y = adj[x * d_ + rnd(deg[x])];
        int dup = 0;
        for (int k = 0; k < cnt; k++) {
            if (xs_[k] == x || ys_[k] == y) { dup = 1; break; }
        }
        if (dup) continue;
        xs_[cnt] = x;
        ys_[cnt] = y;
        cnt++;
    }
    if (cnt < 2) return 0;
    for (int k = 0; k < cnt; k++) del_edge(xs_[k], ys_[k]);
    int a = n_++, b = n_++;
    col[a] = 0; col[b] = 1;
    deg[a] = 0; deg[b] = 0;
    for (int k = 0; k < cnt; k++) {
        add_edge(a, ys_[k]);
        add_edge(xs_[k], b);
    }
    if (cnt < d_) add_edge(a, b);
    fill();
    return 1;
}

/* Metropolis annealing over edge switches. Returns 1 if the graph reaches cost 0. */
static int anneal(long iters, double T0, double T1) {
    long cur = cost();
    if (cur == 0) return 1;
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && cpu() > deadline_s) return 0;
        int a, c;
        do { a = rnd(n_); } while (col[a] != 0 || deg[a] == 0);
        do { c = rnd(n_); } while (col[c] != 0 || deg[c] == 0);
        if (a == c) continue;
        int i = rnd(deg[a]), j = rnd(deg[c]);
        int b = adj[a * d_ + i], e = adj[c * d_ + j];
        if (b == e) continue;
        if (isadj(a, e) || isadj(c, b)) continue;
        sw(a, i, c, j);
        long nw = cost();
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (nw <= cur || rndu() < exp(-(double)(nw - cur) / T)) {
            cur = nw;
        } else {
            sw(a, i, c, j);
        }
    }
    return cur == 0;
}

static void save_best(void) {
    bn = n_;
    memcpy(badj, adj, sizeof(int) * (size_t)n_ * d_);
    memcpy(bdeg, deg, sizeof(int) * (size_t)n_);
}

static void restore_best(void) {
    n_ = bn;
    memcpy(adj, badj, sizeof(int) * (size_t)bn * d_);
    memcpy(deg, bdeg, sizeof(int) * (size_t)bn);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || d_ < 1 || D_ < 2 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    CAP = n0 + 3000;
    WC = (CAP + 63) >> 6;
    adj = malloc(sizeof(int) * (size_t)CAP * d_);
    badj = malloc(sizeof(int) * (size_t)CAP * d_);
    deg = calloc((size_t)CAP, sizeof(int));
    bdeg = calloc((size_t)CAP, sizeof(int));
    col = calloc((size_t)CAP, sizeof(int));
    R = calloc((size_t)CAP * WC, sizeof(uint64_t));
    Q = calloc((size_t)CAP * WC, sizeof(uint64_t));
    int *stk = malloc(sizeof(int) * (size_t)CAP);
    if (!adj || !badj || !deg || !bdeg || !col || !R || !Q || !stk) {
        printf("0 0\n");
        return 0;
    }

    n_ = n0;
    int ok = 1;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (deg[u] >= d_ || deg[v] >= d_ || isadj(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0 && ok; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0 && ok) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adj[u * d_ + k];
                if (col[w] == -1) { col[w] = 1 - col[u]; stk[sp++] = w; }
                else if (col[w] == col[u]) { ok = 0; break; }
            }
        }
    }
    if (!ok || cost() != 0) {
        printf("0 0\n");
        return 0;
    }

    save_best();
    deadline_s = cpu() + budget;

    if (m0 > 0) {
        while (cpu() < deadline_s) {
            if (bn + 2 > CAP) break;
            restore_best();
            if (!grow()) continue;
            if (anneal(ITERS, 0.6, 0.05) && n_ > bn) save_best();
        }
    }

    long m = 0;
    for (int v = 0; v < bn; v++) m += bdeg[v];
    m /= 2;
    printf("%d %ld\n", bn, m);
    for (int v = 0; v < bn; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[v * d_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions.
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _next_prime_power(d):
    q = max(2, d)
    while not lib.is_prime_power(q):
        q += 1
    return q


def _raw_big(d, D, q=None):
    """Dense structured graph with degree q + 1 >= d, to be thinned into a valid graph."""
    if q is None:
        q = _next_prime_power(d)
    if D >= 4:
        if q > 16:
            return None
        return _gq_w(q)
    if q > 13:
        return None
    return lib.projective_plane_incidence(q)


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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Local search for a cover of `full` by at most d candidates (swap moves)."""
    if not cands:
        return None
    k = min(d, len(cands))
    cur = rng.sample(cands, k)

    def cov(S):
        c = 0
        for s in S:
            c |= ball[s]
        return c

    cur_cov = cov(cur)
    cur_score = cur_cov.bit_count()
    for it in range(iters):
        if cur_cov == full:
            return cur
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        inn = rng.choice(cands)
        if inn in cur:
            continue
        trial = cur[:]
        trial[i] = inn
        t_cov = cov(trial)
        t_score = t_cov.bit_count()
        if t_score >= cur_score or rng.random() < 0.02:
            cur, cur_cov, cur_score = trial, t_cov, t_score
    return cur if cur_cov == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Add vertices whose neighbourhoods cover the deficient vertices within D-1."""
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
            for attempt in range(60):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _cover_search(cands, ball, full, d, rng, 1500, deadline)
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
    """Join deficient opposite-side vertices in random order (keeps diameter)."""
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


# ----------------------------------------------------------------------------
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
# ----------------------------------------------------------------------------

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
# Thin a dense structured graph into a valid one.
# ----------------------------------------------------------------------------

def _reduce_degree(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    over = [v for v in range(n) if len(adj[v]) > d]
    while over:
        v = over.pop()
        while len(adj[v]) > d:
            u = max(adj[v], key=lambda x: (len(adj[x]), rng.random()))
            adj[v].discard(u)
            adj[u].discard(v)
            if len(adj[u]) > d:
                over.append(u)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _delete_to_valid(n, edges, d, D, rng, deadline):
    """Delete the worst vertices in batches until the diameter bound holds."""
    adj = {v: set() for v in range(n)}
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    while time.monotonic() < deadline:
        verts = sorted(adj)
        m = len(verts)
        if m == 0:
            return None
        idx = {v: i for i, v in enumerate(verts)}
        nbr = [[idx[u] for u in adj[v]] for v in verts]
        ball = _balls_radius(m, nbr, D)
        bad = [m - b.bit_count() for b in ball]
        if sum(bad) == 0:
            out = [(idx[v], idx[u]) for v in verts for u in adj[v] if v < u]
            return m, out
        order = sorted(range(m), key=lambda i: (-bad[i], rng.random()))
        k = max(1, m // 50)
        for i in order[:k]:
            v = verts[i]
            if v not in adj:
                continue
            for u in adj[v]:
                adj[u].discard(v)
            del adj[v]
    return None


def _deletion_trial(d, D, raw_n, raw_e, rng, deadline):
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Unstructured d-regular bipartite search: degree-preserving insertion plus
# annealing with edge switches. Reverts to the last valid state on failure.
# ----------------------------------------------------------------------------

def _rr_add_pair(adj, left, right, d, rng):
    elist = [(x, y) for x in left for y in adj[x]]
    rng.shuffle(elist)
    xs, ys, picked = set(), set(), []
    for x, y in elist:
        if x in xs or y in ys:
            continue
        xs.add(x)
        ys.add(y)
        picked.append((x, y))
        if len(picked) == d:
            break
    if len(picked) < d:
        return False
    a = len(adj)
    adj.append(set())
    b = len(adj)
    adj.append(set())
    left.append(a)
    right.append(b)
    for x, y in picked:
        adj[x].discard(y)
        adj[y].discard(x)
        adj[a].add(y)
        adj[y].add(a)
        adj[x].add(b)
        adj[b].add(x)
    return True


def _rr_anneal(adj, left, D, rng, iters, deadline):
    elist = [(x, y) for x in left for y in adj[x]]
    cur = _cost(adj, D)
    temp = 0.5
    for _ in range(iters):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            return False
        p = rng.randrange(len(elist))
        q = rng.randrange(len(elist))
        a, b = elist[p]
        c, e = elist[q]
        if a == c or b == e:
            continue
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
            elist[p] = (a, e)
            elist[q] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        temp = max(0.05, temp * 0.9995)
    return cur == 0


def _rr_phase(d, D, deadline, rng, consider):
    h = d
    adj = [set() for _ in range(2 * h)]
    left = list(range(h))
    right = list(range(h, 2 * h))
    for i in range(h):
        for j in right:
            adj[i].add(j)
            adj[j].add(i)
    fails = 0
    while time.monotonic() < deadline:
        snap = ([set(s) for s in adj], list(left), list(right))
        if not _rr_add_pair(adj, left, right, d, rng):
            break
        iters = 2000 if fails == 0 else 6000
        if _rr_anneal(adj, left, D, rng, iters, deadline):
            fails = 0
            e = [(u, v) for u in left for v in adj[u]]
            consider(len(adj), e)
        else:
            adj, left, right = snap
            fails += 1
            if fails >= 3:
                break


# ----------------------------------------------------------------------------
# Bipartite voltage lifts over small groups.
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


def _lift_search(d, D, s, G, mul, rng, deadline):
    """Anneal voltages of a bipartite lift. Returns a valid (n, edges) or None."""
    darts = _random_darts(s, d, G, rng)
    n, e = lib.group_lift(2 * s, darts, G, mul)
    cur = _cost(_to_sets(n, e), D)
    temp = 0.6
    while cur > 0:
        if time.monotonic() > deadline:
            return None
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
    return n, e


def _lift_phase(d, D, get_best, deadline, rng, consider):
    while time.monotonic() < deadline:
        best_n = get_best()
        s = rng.choice((1, 2, 2, 3, 3, 4, 5, 6))
        G_min = best_n // (2 * s) + 1
        G = G_min + rng.randrange(4)
        opts = _group_options(G)
        if not opts:
            continue
        M, k, r = rng.choice(opts)
        try:
            _, mul, _ = lib.semidirect_group(M, k, r)
        except ValueError:
            continue
        slice_end = min(deadline, time.monotonic() + 3.0)
        res = _lift_search(d, D, s, G, mul, rng, slice_end)
        if res is not None:
            n, e = res
            consider(n, e)
            n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# Large-neighbourhood search and pruning (Python fallback).
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Usable budget T = 0.82 * time_limit, split into phases:
#   A  structured base (W(q) or PG(2,q)) grown, then twin/grow trials
#   B  thinned dense structured graph (degree reduction + vertex deletion)
#   R  degree-preserving growth of unstructured d-regular bipartite graphs
#   L  voltage lifts over small groups
#   C  C annealing engine from the best valid graph (LNS fallback in Python)
# Every kept graph passes lib.is_valid. The Haar fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.82 * time_limit

    def at(f):
        return start + f * T

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

    # Phase A: structured base, grown; then twin/grow trials.
    base = None
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
    base_n, base_e = best_n, list(best_e)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        base_n, base_e = n0, list(e0)
        consider(*_grow(n0, e0, d, D, at(0.04), rng))
    if D >= 2:
        trial_end = at(0.12)
        while time.monotonic() < trial_end:
            consider(*_trial(base_n, base_e, d, D, rng, trial_end))

    # Phase B: thinned dense structured graph, repeated with fresh randomness.
    if D >= 2 and time.monotonic() < at(0.35):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.35):
                r = _deletion_trial(d, D, rn, re, rng, at(0.35))
                if r is None:
                    break
                consider(*r)

    # Phase R: unstructured degree-preserving growth with annealing.
    if D >= 2 and d >= 2 and time.monotonic() < at(0.60):
        _rr_phase(d, D, at(0.60), rng, consider)

    # Phase L: voltage lifts over small groups.
    if D >= 2 and time.monotonic() < at(0.70):
        _lift_phase(d, D, lambda: best_n, at(0.70), rng, consider)

    if best_n >= lib.moore_bound(d, D):
        return best_n, list(best_e)

    # Phase C: C annealing engine from the best valid graph. It gets the time
    # up to 0.9 * time_limit, minus a margin for compilation. If it fails, the
    # Python LNS uses the same window.
    if D >= 2 and d >= 2:
        c_end = start + 0.9 * time_limit
        budget = c_end - time.monotonic() - 1.5
        if budget > 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e),
                                timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                _lns(best_n, best_e, d, D, c_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
