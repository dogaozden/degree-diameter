import itertools
import math
import random
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

/* Simulated-annealing repair of a bipartite max-degree-d graph toward diameter <= D.
   Moves: degree-preserving edge switches, edge additions between deficient
   opposite-side vertices, and growth by inserting a new vertex whose neighbourhood
   steals edges from saturated vertices. Cost = number of vertex pairs at distance > D.
   The valid snapshot with the most vertices is printed. */

#define MAXN 4096
#define MAXD 64
#define WMAX 64
#define STALL 6000
#define TEMP 0.35

static int n, d, D;
static int deg[MAXN];
static int adjv[MAXN][MAXD];
static int col[MAXN];
static int sn;
static int sdeg[MAXN];
static int sadj[MAXN][MAXD];
static int scol[MAXN];
static int have_valid;
static int ie_u[MAXN * MAXD / 2 + 8], ie_v[MAXN * MAXD / 2 + 8];
static int m_in;
static uint64_t BUF[2][MAXN][WMAX];
static uint64_t rs;
static int mv_a, mv_b, mv_a2, mv_b2;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adjv[a][k] == b) return 1;
    return 0;
}
static void rm_half(int a, int b) {
    for (int k = 0; k < deg[a]; k++) {
        if (adjv[a][k] == b) {
            adjv[a][k] = adjv[a][--deg[a]];
            return;
        }
    }
}
static void add_edge(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}
static void rm_edge(int a, int b) {
    rm_half(a, b);
    rm_half(b, a);
}

static long bad_pairs(void) {
    int W = (n + 63) / 64;
    uint64_t (*A)[WMAX] = BUF[0];
    uint64_t (*B)[WMAX] = BUF[1];
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) A[v][w] = 0;
        A[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) B[v][w] = A[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjv[v][k];
                for (int w = 0; w < W; w++) B[v][w] |= A[u][w];
            }
        }
        uint64_t (*t)[WMAX] = A;
        A = B;
        B = t;
    }
    long cnt = 0;
    for (int v = 0; v < n; v++) {
        int pc = 0;
        for (int w = 0; w < W; w++) pc += __builtin_popcountll(A[v][w]);
        cnt += n - pc;
    }
    return cnt / 2;
}

static int propose_switch(void) {
    for (int t = 0; t < 50; t++) {
        int a = rndi(n), b, a2, b2;
        if (deg[a] == 0) continue;
        b = adjv[a][rndi(deg[a])];
        if (col[a] == 1) { int tmp = a; a = b; b = tmp; }
        a2 = rndi(n);
        if (deg[a2] == 0) continue;
        b2 = adjv[a2][rndi(deg[a2])];
        if (col[a2] == 1) { int tmp = a2; a2 = b2; b2 = tmp; }
        if (a == a2 || b == b2) continue;
        if (has_edge(a, b2) || has_edge(a2, b)) continue;
        rm_edge(a, b);
        rm_edge(a2, b2);
        add_edge(a, b2);
        add_edge(a2, b);
        mv_a = a; mv_b = b; mv_a2 = a2; mv_b2 = b2;
        return 1;
    }
    return 0;
}

static int propose_add(void) {
    static int x0[MAXN], y1[MAXN];
    int nx = 0, ny = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < d) {
            if (col[v] == 0) x0[nx++] = v;
            else y1[ny++] = v;
        }
    }
    if (nx == 0 || ny == 0) return 0;
    for (int t = 0; t < 30; t++) {
        int x = x0[rndi(nx)], y = y1[rndi(ny)];
        if (!has_edge(x, y)) {
            add_edge(x, y);
            mv_a = x; mv_b = y;
            return 1;
        }
    }
    return 0;
}

static void undo_move(int kind) {
    if (kind == 0) {
        rm_edge(mv_a, mv_b2);
        rm_edge(mv_a2, mv_b);
        add_edge(mv_a, mv_b);
        add_edge(mv_a2, mv_b2);
    } else {
        rm_edge(mv_a, mv_b);
    }
}

static void shuffle_ints(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void insert_vertex(void) {
    static int defi[MAXN], other[MAXN];
    int nc = rndi(2), oc = 1 - nc;
    int nf = 0, no = 0;
    for (int v = 0; v < n; v++) {
        if (col[v] != oc) continue;
        if (deg[v] < d) defi[nf++] = v;
        else other[no++] = v;
    }
    shuffle_ints(defi, nf);
    shuffle_ints(other, no);
    int v = n++;
    deg[v] = 0;
    col[v] = nc;
    int taken = 0;
    for (int i = 0; i < nf && taken < d; i++) {
        add_edge(defi[i], v);
        taken++;
    }
    for (int i = 0; i < no && taken < d; i++) {
        int x = other[i];
        if (deg[x] == 0) continue;
        int y = adjv[x][rndi(deg[x])];
        rm_edge(x, y);
        add_edge(x, v);
        taken++;
    }
}

static void save_state(void) {
    sn = n;
    memcpy(sdeg, deg, sizeof(int) * (size_t)n);
    memcpy(scol, col, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(sadj[v], adjv[v], sizeof(int) * (size_t)deg[v]);
    have_valid = 1;
}

static void restore_state(void) {
    n = sn;
    memcpy(deg, sdeg, sizeof(int) * (size_t)n);
    memcpy(col, scol, sizeof(int) * (size_t)n);
    for (int v = 0; v < n; v++) memcpy(adjv[v], sadj[v], sizeof(int) * (size_t)deg[v]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    double budget = atof(argv[4]);
    double t0 = now_s();

    int nin = 0, min_e = 0;
    if (scanf("%d %d", &nin, &min_e) != 2 || nin < 1 || nin > MAXN - 2 ||
        min_e < 0 || min_e > MAXN * MAXD / 2 || d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    n = nin;
    int ok = 1;
    for (int i = 0; i < min_e; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
        add_edge(u, v);
        ie_u[i] = u;
        ie_v[i] = v;
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }
    m_in = min_e;

    /* 2-colour (graph must be bipartite). */
    for (int v = 0; v < n; v++) col[v] = -1;
    static int stk[MAXN];
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int k = 0; k < deg[u]; k++) {
                int w = adjv[u][k];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                } else if (col[w] == col[u]) {
                    ok = 0;
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    long cur = bad_pairs();
    if (cur == 0) save_state();
    long minc = cur;
    long it = 0, last = 0;

    while (now_s() - t0 < budget) {
        it++;
        if (cur == 0) {
            if (!have_valid || n > sn) save_state();
            if (n >= MAXN - 2) break;
            insert_vertex();
            cur = bad_pairs();
            minc = cur;
            last = it;
            continue;
        }
        if (it - last > STALL) {
            if (have_valid) {
                restore_state();
                cur = bad_pairs();
            }
            minc = cur;
            last = it;
            continue;
        }
        int kind, done;
        if (rndi(10) >= 8) {
            kind = 1;
            done = propose_add();
        } else {
            kind = 0;
            done = propose_switch();
        }
        if (!done) continue;
        long nc = bad_pairs();
        long delta = nc - cur;
        int acc = 1;
        if (delta > 0 && !(rndu() < exp(-(double)delta / TEMP))) acc = 0;
        if (acc) {
            cur = nc;
            if (cur < minc) {
                minc = cur;
                last = it;
            }
        } else {
            undo_move(kind);
        }
    }

    if (have_valid) {
        restore_state();
        long m2 = 0;
        for (int v = 0; v < n; v++) m2 += deg[v];
        m2 /= 2;
        printf("%d %ld\n", n, m2);
        for (int u = 0; u < n; u++)
            for (int k = 0; k < deg[u]; k++)
                if (u < adjv[u][k]) printf("%d %d\n", u, adjv[u][k]);
    } else {
        printf("%d %d\n", nin, m_in);
        for (int i = 0; i < m_in; i++) printf("%d %d\n", ie_u[i], ie_v[i]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Constructions: PG(2,q) incidence and the generalized quadrangle W(q).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4, order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """PG(2,q) incidence for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Twin extension: a twin of x keeps all old distances and needs one spare
# degree on each neighbour of x.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    order = list(range(n))
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


# ----------------------------------------------------------------------------
# Cover-based vertex extension and saturation.
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
    """Cover-extend first, then saturate with leftover spare degree."""
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
# Voltage lifts over non-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


# ----------------------------------------------------------------------------
# Haar and cyclic-lift families.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def t_at(frac):
        return start + frac * time_limit

    moore = lib.moore_bound(d, D)

    # Stage 1 (D >= 3): projective planes, grown by cover extension.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, t_at(0.15) - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _grow(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # Stage 2 (D >= 4): W(q), then cover growth, then twins, then cover growth again.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, t_at(0.2), rng)
            consider(n2, e2)
            tn, te = _twin_grow(gq[0], gq[1], d, rng, t_at(0.23))
            consider(tn, te)
            n4, e4 = _grow(tn, te, d, D, t_at(0.3), rng)
            consider(n4, e4)

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= moore:
        return best

    # Stage 3: group lifts (D >= 4 favoured), Haar and cyclic lifts, until 0.4 of budget.
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0
    lift_deadline = t_at(0.4)

    while time.monotonic() < lift_deadline and best_n < moore:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, lift_deadline)
            if res is not None:
                consider(res[0], res[1])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, lift_deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], best_n // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, lift_deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    # Stage 4: simulated-annealing repair and vertex insertion in C from the best graph.
    end_all = t_at(0.8)
    remaining = end_all - time.monotonic()
    if D >= 2 and best_n < moore and remaining >= 3.0:
        budget = round(remaining - 1.5, 2)
        try:
            txt = lib.run_c(C_SOURCE, [d, D, seed, budget],
                            stdin_graph=best, timeout=budget + 30.0)
            n3, e3 = lib.parse_graph_text(txt)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
