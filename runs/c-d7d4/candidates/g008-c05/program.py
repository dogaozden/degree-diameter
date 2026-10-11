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

#define CAP_MAX 6000
#define DMAX 64

static int d_, D_, cap_, Wcap_;
static uint64_t rs_;
static uint64_t *bA, *bB, *cov;
static int *fl, *fr, *side0;

typedef struct { int n; int *deg; int *col; int *adj; } State;

static uint64_t rnd64(void) { rs_ ^= rs_ << 13; rs_ ^= rs_ >> 7; rs_ ^= rs_ << 17; return rs_; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static State st_new(void) {
    State s;
    s.n = 0;
    s.deg = calloc((size_t)cap_, sizeof(int));
    s.col = calloc((size_t)cap_, sizeof(int));
    s.adj = calloc((size_t)cap_ * d_, sizeof(int));
    if (!s.deg || !s.col || !s.adj) { fprintf(stderr, "oom\n"); exit(1); }
    return s;
}

static void st_copy(State *dst, const State *src) {
    dst->n = src->n;
    memcpy(dst->deg, src->deg, sizeof(int) * (size_t)src->n);
    memcpy(dst->col, src->col, sizeof(int) * (size_t)src->n);
    memcpy(dst->adj, src->adj, sizeof(int) * (size_t)src->n * d_);
}

static int has_edge(const State *S, int u, int v) {
    const int *a = S->adj + (size_t)u * d_;
    for (int k = 0; k < S->deg[u]; k++) if (a[k] == v) return 1;
    return 0;
}

static void del_arc(State *S, int u, int v) {
    int *a = S->adj + (size_t)u * d_;
    int dg = S->deg[u];
    for (int k = 0; k < dg; k++) {
        if (a[k] == v) { a[k] = a[dg - 1]; S->deg[u]--; return; }
    }
}

static void add_edge(State *S, int u, int v) {
    S->adj[(size_t)u * d_ + S->deg[u]++] = v;
    S->adj[(size_t)v * d_ + S->deg[v]++] = u;
}

static void remove_edge(State *S, int u, int v) {
    del_arc(S, u, v);
    del_arc(S, v, u);
}

static void remove_vertex(State *S, int x) {
    int n = S->n, last = n - 1;
    while (S->deg[x] > 0) {
        int y = S->adj[(size_t)x * d_ + S->deg[x] - 1];
        S->deg[x]--;
        del_arc(S, y, x);
    }
    if (x != last) {
        for (int k = 0; k < S->deg[last]; k++) {
            int y = S->adj[(size_t)last * d_ + k];
            int *ay = S->adj + (size_t)y * d_;
            for (int j = 0; j < S->deg[y]; j++) if (ay[j] == last) { ay[j] = x; break; }
        }
        memcpy(S->adj + (size_t)x * d_, S->adj + (size_t)last * d_, sizeof(int) * d_);
        S->deg[x] = S->deg[last];
        S->col[x] = S->col[last];
    }
    S->deg[last] = 0;
    S->n = last;
}

static void compute_balls(const State *S, int r, uint64_t *out, uint64_t *tmp) {
    int n = S->n, W = (n + 63) >> 6;
    memset(out, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) out[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            uint64_t *t = tmp + (size_t)v * W;
            memcpy(t, out + (size_t)v * W, sizeof(uint64_t) * W);
            for (int k = 0; k < S->deg[v]; k++) {
                const uint64_t *w = out + (size_t)S->adj[(size_t)v * d_ + k] * W;
                for (int j = 0; j < W; j++) t[j] |= w[j];
            }
        }
        memcpy(out, tmp, sizeof(uint64_t) * (size_t)n * W);
    }
}

static long cost_of(const State *S) {
    compute_balls(S, D_, bA, bB);
    int n = S->n, W = (n + 63) >> 6;
    long tot = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int j = 0; j < W; j++) c += pc64(bA[(size_t)v * W + j]);
        tot += n - c;
    }
    return tot / 2;
}

/* Bipartite double-edge switches (degrees kept) minimising bad pairs. */
static long anneal(State *S, int iters, clock_t dl) {
    int n = S->n, m = 0;
    for (int v = 0; v < n; v++) if (S->col[v] == 0) side0[m++] = v;
    long cur = cost_of(S);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && clock() > dl) break;
        if (m < 2) break;
        int a = side0[rndi(m)];
        if (S->deg[a] == 0) continue;
        int b = S->adj[(size_t)a * d_ + rndi(S->deg[a])];
        int c = side0[rndi(m)];
        if (c == a || S->deg[c] == 0) continue;
        int e = S->adj[(size_t)c * d_ + rndi(S->deg[c])];
        if (has_edge(S, a, e) || has_edge(S, c, b)) continue;
        remove_edge(S, a, b);
        remove_edge(S, c, e);
        add_edge(S, a, e);
        add_edge(S, c, b);
        long nw = cost_of(S);
        if (nw <= cur || (nw == cur + 1 && rndi(10) == 0)) {
            cur = nw;
        } else {
            remove_edge(S, a, e);
            remove_edge(S, c, b);
            add_edge(S, a, b);
            add_edge(S, c, e);
        }
    }
    return cur;
}

static void shuffle_int(int *x, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = x[i]; x[i] = x[j]; x[j] = t;
    }
}

/* Join deficient opposite-side vertices in random order. */
static void fill(State *S) {
    int n = S->n, nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (S->deg[v] < d_) {
            if (S->col[v] == 0) fl[nl++] = v; else fr[nr++] = v;
        }
    }
    shuffle_int(fl, nl);
    shuffle_int(fr, nr);
    for (int i = 0; i < nl; i++) {
        int a = fl[i];
        for (int j = 0; j < nr; j++) {
            if (S->deg[a] >= d_) break;
            int b = fr[j];
            if (S->deg[b] < d_ && !has_edge(S, a, b)) add_edge(S, a, b);
        }
    }
}

/* Add a vertex on the opposite side of `side`, joined to a greedy cover of the old vertices. */
static void add_vertex(State *S, int side) {
    int nold = S->n;
    if (nold + 1 > cap_) return;
    int v = nold;
    S->n = nold + 1;
    S->col[v] = 1 - side;
    S->deg[v] = 0;
    compute_balls(S, D_ - 1, bA, bB);
    int W = (S->n + 63) >> 6;
    memset(cov, 0, sizeof(uint64_t) * W);
    int chosen[DMAX];
    int nc = 0;
    for (int k = 0; k < d_; k++) {
        int best = -1;
        long bs = -1;
        for (int s = 0; s < nold; s++) {
            if (S->col[s] != side) continue;
            int taken = 0;
            for (int i = 0; i < nc; i++) if (chosen[i] == s) { taken = 1; break; }
            if (taken) continue;
            long g = 0;
            const uint64_t *b = bA + (size_t)s * W;
            for (int j = 0; j < W; j++) g += pc64(b[j] & ~cov[j]);
            long sc = g * 1024 + rndi(1024);
            if (sc > bs) { bs = sc; best = s; }
        }
        if (best < 0 || bs < 1024) break;
        chosen[nc++] = best;
        for (int j = 0; j < W; j++) cov[j] |= bA[(size_t)best * W + j];
    }
    for (int i = 0; i < nc; i++) {
        int s = chosen[i];
        if (S->deg[s] >= d_) {
            int t = S->adj[(size_t)s * d_ + rndi(S->deg[s])];
            remove_edge(S, s, t);
        }
        add_edge(S, s, v);
    }
}

static void make_kdd(State *S, int d) {
    memset(S->deg, 0, sizeof(int) * cap_);
    S->n = 2 * d;
    for (int i = 0; i < 2 * d; i++) S->col[i] = (i < d) ? 0 : 1;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(S, i, d + j);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs_ = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (!rs_) rs_ = 1;
    clock_t t0 = clock();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    int *eu = malloc(sizeof(int) * (m0 + 1));
    int *ev = malloc(sizeof(int) * (m0 + 1));
    int mr = 0;
    for (int i = 0; i < m0; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        eu[mr] = a; ev[mr] = b; mr++;
    }

    if (d_ < 3 || D_ < 2 || d_ > DMAX) {
        printf("%d %d\n", n0, mr);
        for (int i = 0; i < mr; i++) printf("%d %d\n", eu[i], ev[i]);
        return 0;
    }

    double s = 0, p = 1;
    for (int i = 0; i < D_; i++) { s += p; p *= (d_ - 1); }
    double mo = 2.0 * s;
    if (mo > CAP_MAX) mo = CAP_MAX;
    int target = (int)mo;
    cap_ = (int)mo + 2;
    if (n0 + 2 > cap_) cap_ = n0 + 2;
    Wcap_ = (cap_ + 63) >> 6;

    bA = malloc(sizeof(uint64_t) * (size_t)cap_ * Wcap_);
    bB = malloc(sizeof(uint64_t) * (size_t)cap_ * Wcap_);
    cov = malloc(sizeof(uint64_t) * (size_t)Wcap_ + 8);
    fl = malloc(sizeof(int) * cap_);
    fr = malloc(sizeof(int) * cap_);
    side0 = malloc(sizeof(int) * cap_);
    if (!bA || !bB || !cov || !fl || !fr || !side0) return 1;

    State work = st_new(), cur = st_new(), best = st_new();

    if (n0 == 0) {
        make_kdd(&work, d_);
    } else {
        work.n = n0;
        for (int v = 0; v < n0; v++) work.col[v] = -1;
        for (int i = 0; i < mr; i++) {
            int a = eu[i], b = ev[i];
            if (a < 0 || b < 0 || a >= n0 || b >= n0 || a == b) continue;
            if (has_edge(&work, a, b)) continue;
            if (work.deg[a] >= d_ || work.deg[b] >= d_) continue;
            add_edge(&work, a, b);
        }
        for (int s0 = 0; s0 < n0; s0++) {
            if (work.col[s0] != -1) continue;
            work.col[s0] = 0;
            int qh = 0, qt = 0;
            side0[qt++] = s0;
            while (qh < qt) {
                int v = side0[qh++];
                for (int k = 0; k < work.deg[v]; k++) {
                    int u = work.adj[(size_t)v * d_ + k];
                    if (work.col[u] == -1) {
                        work.col[u] = 1 - work.col[v];
                        side0[qt++] = u;
                    }
                }
            }
        }
        if (cost_of(&work) != 0) make_kdd(&work, d_);
    }

    st_copy(&best, &work);
    st_copy(&cur, &work);
    clock_t dl = t0 + (clock_t)(tl * CLOCKS_PER_SEC);

    while (clock() < dl && best.n < target) {
        st_copy(&work, &cur);
        int r = rndi(5);
        if (r < 2) {
            add_vertex(&work, rndi(2));
        } else {
            int k = 1 + rndi(3);
            for (int i = 0; i < k; i++) {
                if (work.n > 4) remove_vertex(&work, rndi(work.n));
            }
        }
        fill(&work);
        long c = anneal(&work, 300, dl);
        if (c == 0) {
            if (work.n > best.n) st_copy(&best, &work);
            if (work.n >= cur.n - 1) st_copy(&cur, &work);
        }
        if (cur.n < best.n - 3) st_copy(&cur, &best);
    }

    long m = 0;
    for (int v = 0; v < best.n; v++) m += best.deg[v];
    m /= 2;
    printf("%d %ld\n", best.n, m);
    for (int v = 0; v < best.n; v++) {
        for (int k = 0; k < best.deg[v]; k++) {
            int u = best.adj[(size_t)v * d_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured bases (Python).
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
    """Generalized quadrangle incidence graph W(q), largest prime power q <= min(d-1, 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python-side growth helpers (cover vertices, twins, saturation).
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
    """Greedily add vertices whose neighbourhoods cover all vertices within distance D."""
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
    """Join deficient opposite-side vertices (keeps bipartite, degrees <= d, distances shrink)."""
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    rng = random.Random(seed)
    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base: GQ for D >= 4, projective plane for D = 3.
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        pre_end = start + 0.12 * time_limit
        n1, e1 = _grow(n0, e0, d, D, pre_end, rng)
        consider(n1, e1)
        n2, e2 = _duplicate_twins(n1, e1, d, rng)
        e2 = _saturate_edges(n2, e2, d, rng)
        n2, e2 = _grow(n2, e2, d, D, pre_end, rng, attempts=30)
        consider(n2, e2)

    # C engine: anneal-repaired add/kill-regrow search from the best graph so far.
    elapsed = time.monotonic() - start
    budget = 0.85 * time_limit - elapsed - 1.0
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed & 0x7FFFFFFF, round(budget, 2)],
                             stdin_graph=(best_n, best_e),
                             timeout=max(2.0, time_limit - elapsed - 2.0))
            n, e = lib.parse_graph_text(text)
            consider(n, e)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
