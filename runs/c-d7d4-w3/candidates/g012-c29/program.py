import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset annealing with vertex insertion.
#
# The state is a bipartite graph with max degree d. Every move keeps the
# bipartition and the degree bound, so the output is always valid bipartite
# with max degree <= d. The objective is the number of vertex pairs at distance
# more than D, computed exactly with radius-D bitset balls.
#
# Moves:
#   switch : bipartite double-edge swap (degrees unchanged)
#   fill   : add edges between deficient vertices on opposite sides
#   grow   : new vertex v takes d neighbours b_i on the other side, and each b_i
#            gives up one old edge (a_i, b_i). This adds one vertex without
#            touching the degree of any b_i.
# Annealing repairs the diameter after each growth. When it fails for too many
# stages, the engine restores the best valid graph and grows again.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define STAGE 2000
#define FAILLIM 40

static int DEG, RAD, CAP, WC, NV;
static int *deg, *adjv, *side, *tmp0, *tmp1, *queue_buf;
static u64 *BA, *BB;
static u64 RS = 88172645463325252ULL;
static double T0, BUDGET;
static int bestn = 0, bestm = 0;
static int *bu, *bv, *bside;

static u64 rnd(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}

static int rndint(int m) { return (int)(rnd() % (u64)m); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)clock() / CLOCKS_PER_SEC - T0; }

static int pop64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    int b = u * DEG;
    for (int k = 0; k < deg[u]; k++)
        if (adjv[b + k] == v) return 1;
    return 0;
}

static void add_arc(int u, int v) {
    adjv[u * DEG + deg[u]] = v;
    deg[u]++;
}

static void del_arc(int u, int v) {
    int b = u * DEG;
    for (int k = 0; k < deg[u]; k++) {
        if (adjv[b + k] == v) {
            adjv[b + k] = adjv[b + deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void add_edge(int u, int v) {
    add_arc(u, v);
    add_arc(v, u);
}

static void remove_edge(int u, int v) {
    del_arc(u, v);
    del_arc(v, u);
}

/* Number of unordered vertex pairs at distance > RAD. */
static long bad_pairs(void) {
    int n = NV;
    if (n == 0) return 0;
    int w = (n + 63) >> 6;
    u64 *A = BA, *B = BB;
    for (int v = 0; v < n; v++) {
        u64 *row = A + (size_t)v * WC;
        for (int j = 0; j < w; j++) row[j] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < RAD; r++) {
        for (int v = 0; v < n; v++) {
            u64 *dst = B + (size_t)v * WC;
            u64 *src = A + (size_t)v * WC;
            for (int j = 0; j < w; j++) dst[j] = src[j];
            int b = v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                u64 *s2 = A + (size_t)adjv[b + k] * WC;
                for (int j = 0; j < w; j++) dst[j] |= s2[j];
            }
        }
        u64 *t = A;
        A = B;
        B = t;
    }
    long tot = 0;
    for (int v = 0; v < n; v++) {
        u64 *s = A + (size_t)v * WC;
        for (int j = 0; j < w; j++) tot += pop64(s[j]);
    }
    return ((long)n * n - tot) / 2;
}

static int try_switch(int *a, int *b, int *c, int *e) {
    int A = rndint(NV);
    if (deg[A] == 0) return 0;
    int B = adjv[A * DEG + rndint(deg[A])];
    int C = rndint(NV);
    if (C == A || side[C] != side[A] || deg[C] == 0) return 0;
    int E = adjv[C * DEG + rndint(deg[C])];
    if (has_edge(A, E) || has_edge(C, B)) return 0;
    *a = A; *b = B; *c = C; *e = E;
    return 1;
}

static void apply_switch(int a, int b, int c, int e) {
    remove_edge(a, b);
    remove_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}

static void undo_switch(int a, int b, int c, int e) {
    remove_edge(a, e);
    remove_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Add cross-side edges between deficient vertices. Only lowers the cost. */
static void fill_edges(void) {
    int n0 = 0, n1 = 0;
    for (int v = 0; v < NV; v++) {
        if (deg[v] >= DEG) continue;
        if (side[v] == 0) tmp0[n0++] = v;
        else tmp1[n1++] = v;
    }
    shuffle_int(tmp0, n0);
    shuffle_int(tmp1, n1);
    for (int i = 0; i < n0; i++) {
        int a = tmp0[i];
        for (int j = 0; j < n1 && deg[a] < DEG; j++) {
            int b = tmp1[j];
            if (deg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

/* Insert one vertex, taking one edge from each of up to DEG other-side vertices. */
static int grow_vertex(void) {
    int old = NV;
    if (old < 2 || old >= CAP) return 0;
    int s = rndint(2);
    int v = old;
    NV = old + 1;
    side[v] = s;
    deg[v] = 0;
    int chosen = 0;
    long tries = 0, limit = 200L * old;
    while (chosen < DEG && tries < limit) {
        tries++;
        int b = rndint(old);
        if (side[b] == s || deg[b] == 0 || has_edge(v, b)) continue;
        int a = adjv[b * DEG + rndint(deg[b])];
        remove_edge(a, b);
        add_edge(v, b);
        chosen++;
    }
    if (chosen == 0) {
        NV = old;
        return 0;
    }
    return chosen;
}

static long anneal(long iters, double thi, double tlo) {
    long cur = bad_pairs();
    fill_edges();
    cur = bad_pairs();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && elapsed() > BUDGET) break;
        double frac = (double)it / (double)iters;
        double T = thi * pow(tlo / thi, frac);
        int a, b, c, e;
        if (!try_switch(&a, &b, &c, &e)) continue;
        apply_switch(a, b, c, e);
        long nc = bad_pairs();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
            cur = nc;
        } else {
            undo_switch(a, b, c, e);
        }
    }
    return cur;
}

static void save_best(void) {
    bestn = NV;
    bestm = 0;
    for (int v = 0; v < NV; v++) {
        bside[v] = side[v];
        for (int k = 0; k < deg[v]; k++) {
            int u = adjv[v * DEG + k];
            if (u > v) {
                bu[bestm] = v;
                bv[bestm] = u;
                bestm++;
            }
        }
    }
}

static void restore_best(void) {
    if (bestn == 0) return;
    NV = bestn;
    for (int v = 0; v < CAP; v++) deg[v] = 0;
    for (int v = 0; v < NV; v++) side[v] = bside[v];
    for (int i = 0; i < bestm; i++) add_edge(bu[i], bv[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    RS ^= (u64)strtoull(argv[3], NULL, 10) * 2654435761ULL + 1ULL;
    if (RS == 0) RS = 1;
    BUDGET = atof(argv[4]);
    T0 = (double)clock() / CLOCKS_PER_SEC;
    DEG = d;
    RAD = D;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0 || d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    CAP = 2 * n0 + 200;
    WC = (CAP + 63) >> 6;
    deg = calloc(CAP, sizeof(int));
    side = calloc(CAP, sizeof(int));
    bside = calloc(CAP, sizeof(int));
    adjv = calloc((size_t)CAP * DEG, sizeof(int));
    tmp0 = calloc(CAP, sizeof(int));
    tmp1 = calloc(CAP, sizeof(int));
    queue_buf = calloc(CAP, sizeof(int));
    bu = calloc((size_t)CAP * DEG + 1, sizeof(int));
    bv = calloc((size_t)CAP * DEG + 1, sizeof(int));
    BA = calloc((size_t)CAP * WC, sizeof(u64));
    BB = calloc((size_t)CAP * WC, sizeof(u64));
    if (!deg || !side || !bside || !adjv || !tmp0 || !tmp1 || !queue_buf ||
        !bu || !bv || !BA || !BB) {
        printf("0 0\n");
        return 0;
    }

    int ok = 1;
    NV = n0;
    for (int i = 0; i < m0 && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) { ok = 0; break; }
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
    }
    /* Bipartition check (also sets sides). */
    for (int v = 0; v < n0; v++) side[v] = -1;
    for (int s = 0; s < n0 && ok; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int qh = 0, qt = 0;
        queue_buf[qt++] = s;
        while (qh < qt && ok) {
            int x = queue_buf[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adjv[x * DEG + k];
                if (side[y] == -1) {
                    side[y] = 1 - side[x];
                    queue_buf[qt++] = y;
                } else if (side[y] == side[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long cur = bad_pairs();
    if (cur == 0) save_best();

    int fails = 0;
    while (elapsed() < BUDGET) {
        if (cur == 0) {
            if (NV > bestn) save_best();
            if (grow_vertex()) fill_edges();
            cur = bad_pairs();
            fails = 0;
        } else {
            cur = anneal(STAGE, 1.0, 0.05);
            if (cur > 0 && ++fails >= FAILLIM) {
                restore_best();
                fill_edges();
                cur = bad_pairs();
                fails = 0;
            }
        }
    }
    if (cur == 0 && NV > bestn) save_best();

    if (bestn == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestn, bestm);
    for (int i = 0; i < bestm; i++) printf("%d %d\n", bu[i], bv[i]);
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for the structured growth phase.
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


def _cover_search(cands, ball, full, d, rng, iters, deadline):
    """Swap-based local search for a cover of `full` by at most d candidates."""
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
    """Greedily add vertices whose neighbourhoods cover the deficient vertices."""
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
    """Greedily join deficient opposite-side vertices in random order. Keeps degrees <= d."""
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
    """Greedily add non-adjacent twins while neighbours have spare degree."""
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
    """One randomized Python pipeline: twins, cover growth and saturation."""
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
# Driver. Python builds the structured start (about 30% of the time), then the C
# engine grows and repairs it for the rest of the budget. Every candidate is
# checked with lib.is_valid before it is kept. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    mb = lib.moore_bound(d, D)
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    py_end = start + 0.30 * time_limit

    # Structured base, grown in Python.
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
        n1, e1 = _grow(n0, e0, d, D, py_end, rng)
        consider(n1, e1)

    if best_n >= mb:
        return best_n, list(best_e)

    if D >= 2:
        while time.monotonic() < py_end and best_n < mb:
            n, e = _trial(base_n, base_e, d, D, rng, py_end)
            consider(n, e)

    # Bitset annealing with vertex insertion in C, from the best graph so far.
    if D >= 2 and best_n < mb:
        cend = start + 0.86 * time_limit
        remaining = cend - time.monotonic()
        if remaining > 4.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining - 2.0:.2f}"],
                                stdin_graph=(best_n, best_e),
                                timeout=remaining + 2.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
