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

typedef uint64_t u64;

#define MAXCAP 4000
#define ITERS_ADD 500
#define ITERS_PERT 300
#define TEMPER 0.6

static int dg, DM;            /* max degree, diameter */
static int cap, NS;           /* vertex capacity, words per bitset row */
static int n, m;              /* current vertex count, edge count */
static int *col, *deg, *nd, *nbr;
static int *EU, *EV;          /* edge list; EU on side 0, EV on side 1 */
static unsigned char *A;      /* adjacency matrix cap*cap */
static u64 *bufA, *bufB, *cov;
static int *chosen, *L0, *L1;
static u64 rs = 88172645463325252ULL;

#define AT(u, v) A[(size_t)(u) * (size_t)cap + (size_t)(v)]

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rndd(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void build_lists(void) {
    int e, v;
    for (v = 0; v < n; v++) nd[v] = 0;
    for (e = 0; e < m; e++) {
        int u = EU[e], w = EV[e];
        if (nd[u] < dg) nbr[u * dg + nd[u]++] = w;
        if (nd[w] < dg) nbr[w * dg + nd[w]++] = u;
    }
}

/* Bitset of all vertices within distance r of each vertex. */
static u64 *balls(int r) {
    int w, v, t, k;
    int nw = (n + 63) / 64;
    u64 *cur = bufA, *nxt = bufB;
    build_lists();
    memset(cur, 0, sizeof(u64) * (size_t)n * NS);
    for (v = 0; v < n; v++) cur[(size_t)v * NS + (v >> 6)] |= 1ULL << (v & 63);
    for (t = 0; t < r; t++) {
        for (v = 0; v < n; v++) {
            u64 *dst = nxt + (size_t)v * NS;
            const u64 *src = cur + (size_t)v * NS;
            for (w = 0; w < nw; w++) dst[w] = src[w];
            for (k = 0; k < nd[v]; k++) {
                const u64 *s2 = cur + (size_t)nbr[v * dg + k] * NS;
                for (w = 0; w < nw; w++) dst[w] |= s2[w];
            }
        }
        {
            u64 *tmp = cur; cur = nxt; nxt = tmp;
        }
    }
    return cur;
}

/* Number of unordered vertex pairs at distance > r (unreachable pairs count). */
static long long bad_pairs(int r) {
    u64 *b = balls(r);
    int nw = (n + 63) / 64, v, w;
    long long tot = 0;
    for (v = 0; v < n; v++) {
        int c = 0;
        for (w = 0; w < nw; w++) c += pc64(b[(size_t)v * NS + w]);
        tot += n - c;
    }
    return tot / 2;
}

static void add_edge(int a, int b) {
    int s0 = (col[a] == 0) ? a : b;
    int s1 = (s0 == a) ? b : a;
    EU[m] = s0; EV[m] = s1; m++;
    AT(s0, s1) = 1; AT(s1, s0) = 1;
    deg[a]++; deg[b]++;
}

static void remove_edge_idx(int i) {
    int u = EU[i], v = EV[i];
    AT(u, v) = 0; AT(v, u) = 0;
    deg[u]--; deg[v]--;
    m--;
    EU[i] = EU[m]; EV[i] = EV[m];
}

/* Degree-preserving bipartite switch: (a,b),(c,e) -> (a,e),(c,b). */
static int apply_switch(int i, int j) {
    int a, b, c, e;
    if (i == j) return 0;
    a = EU[i]; b = EV[i]; c = EU[j]; e = EV[j];
    if (a == c || b == e) return 0;
    if (AT(a, e) || AT(c, b)) return 0;
    AT(a, b) = 0; AT(b, a) = 0; AT(c, e) = 0; AT(e, c) = 0;
    AT(a, e) = 1; AT(e, a) = 1; AT(c, b) = 1; AT(b, c) = 1;
    EV[i] = e; EV[j] = b;
    return 1;
}

static void undo_switch(int i, int j) {
    int a = EU[i], e = EV[i], c = EU[j], b = EV[j];
    AT(a, e) = 0; AT(e, a) = 0; AT(c, b) = 0; AT(b, c) = 0;
    AT(a, b) = 1; AT(b, a) = 1; AT(c, e) = 1; AT(e, c) = 1;
    EV[i] = b; EV[j] = e;
}

/* Simulated annealing over switches, minimising bad pairs. Returns 1 if cost reaches 0. */
static int anneal(int iters, double T) {
    long long cur = bad_pairs(DM);
    int it;
    for (it = 0; it < iters && cur > 0 && m >= 2; it++) {
        int i = rndi(m), j = rndi(m);
        long long nb;
        if (!apply_switch(i, j)) continue;
        nb = bad_pairs(DM);
        if (nb <= cur || rndd() < exp(-(double)(nb - cur) / T)) cur = nb;
        else undo_switch(i, j);
    }
    return cur == 0;
}

/* Add spare-degree edges between deficient opposite-side vertices (only helps distances). */
static void fill(void) {
    int n0 = 0, n1 = 0, i, j, v;
    for (v = 0; v < n; v++) {
        if (deg[v] < dg) {
            if (col[v] == 0) L0[n0++] = v; else L1[n1++] = v;
        }
    }
    for (i = n0 - 1; i > 0; i--) { j = rndi(i + 1); v = L0[i]; L0[i] = L0[j]; L0[j] = v; }
    for (i = n1 - 1; i > 0; i--) { j = rndi(i + 1); v = L1[i]; L1[i] = L1[j]; L1[j] = v; }
    for (i = 0; i < n0; i++) {
        int a = L0[i];
        for (j = 0; j < n1 && deg[a] < dg; j++) {
            int b = L1[j];
            if (deg[b] < dg && !AT(a, b)) add_edge(a, b);
        }
    }
}

/* Add one vertex on `side`, joined to a greedy cover of the opposite side's
   radius-(D-1) balls; full neighbours give up a random edge (stealing). */
static int add_vertex(int side) {
    int nw, pick, nc = 0, k, s, best, w, v;
    long long bsc;
    u64 *bb;
    if (n >= cap) return 0;
    nw = (n + 63) / 64;
    bb = balls(DM - 1);
    memset(cov, 0, sizeof(u64) * NS);
    for (pick = 0; pick < dg; pick++) {
        best = -1; bsc = -1;
        for (s = 0; s < n; s++) {
            int used = 0, g = 0;
            long long sc;
            if (col[s] != 1 - side) continue;
            for (k = 0; k < nc; k++) if (chosen[k] == s) { used = 1; break; }
            if (used) continue;
            for (w = 0; w < nw; w++) g += pc64(bb[(size_t)s * NS + w] & ~cov[w]);
            if (g == 0) continue;
            sc = (long long)g * 16 + rndi(16);
            if (sc > bsc) { bsc = sc; best = s; }
        }
        if (best < 0) break;
        chosen[nc++] = best;
        for (w = 0; w < nw; w++) cov[w] |= bb[(size_t)best * NS + w];
    }
    if (nc == 0) return 0;
    v = n;
    col[v] = side; deg[v] = 0; n++;
    for (k = 0; k < nc; k++) {
        s = chosen[k];
        if (deg[s] >= dg) {
            int cnt = 0, pe = -1, e;
            for (e = 0; e < m; e++) {
                if (EU[e] == s || EV[e] == s) {
                    cnt++;
                    if (rndi(cnt) == 0) pe = e;
                }
            }
            if (pe < 0) continue;
            remove_edge_idx(pe);
        }
        add_edge(v, s);
    }
    fill();
    return 1;
}

typedef struct { int n, m; int *U, *V; } Snap;

static Snap snap_new(void) {
    Snap s;
    s.n = 0; s.m = 0;
    s.U = malloc(sizeof(int) * (size_t)cap * dg + 16);
    s.V = malloc(sizeof(int) * (size_t)cap * dg + 16);
    return s;
}

static void snap_save(Snap *s) {
    s->n = n; s->m = m;
    if (m > 0) {
        memcpy(s->U, EU, sizeof(int) * m);
        memcpy(s->V, EV, sizeof(int) * m);
    }
}

static void snap_restore(const Snap *s) {
    int e, v;
    for (e = 0; e < m; e++) { AT(EU[e], EV[e]) = 0; AT(EV[e], EU[e]) = 0; }
    for (v = 0; v < n; v++) deg[v] = 0;
    n = s->n; m = s->m;
    if (m > 0) {
        memcpy(EU, s->U, sizeof(int) * m);
        memcpy(EV, s->V, sizeof(int) * m);
    }
    for (e = 0; e < m; e++) {
        AT(EU[e], EV[e]) = 1; AT(EV[e], EU[e]) = 1;
        deg[EU[e]]++; deg[EV[e]]++;
    }
}

int main(int argc, char **argv) {
    int n0, m0, i, e, v;
    unsigned long long seed;
    double tl, mbd = 0.0, pw = 1.0;
    long long mb;
    int *IU, *IV, *Q;
    Snap init, tmp, best;
    clock_t t0;
    long long c0;

    if (argc < 5) return 1;
    dg = atoi(argv[1]);
    DM = atoi(argv[2]);
    seed = strtoull(argv[3], NULL, 10);
    tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (i = 0; i < 20; i++) rnd();

    if (dg < 1 || DM < 2) { printf("1 0\n"); return 0; }
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXCAP - 8 || m0 < 0) {
        printf("1 0\n");
        return 0;
    }

    for (i = 0; i < DM; i++) {
        mbd += pw;
        pw *= (dg - 1);
        if (pw > 1e7) pw = 1e7;
    }
    mb = (long long)(2.0 * mbd);
    cap = (int)((mb + 2 > MAXCAP) ? MAXCAP : mb + 2);
    if (cap < n0 + 2) cap = n0 + 2;
    if (cap > MAXCAP) cap = MAXCAP;
    NS = (cap + 63) / 64;

    col = malloc(sizeof(int) * cap);
    deg = calloc(cap, sizeof(int));
    nd = calloc(cap, sizeof(int));
    nbr = malloc(sizeof(int) * (size_t)cap * dg);
    EU = malloc(sizeof(int) * (size_t)cap * dg + 16);
    EV = malloc(sizeof(int) * (size_t)cap * dg + 16);
    A = calloc((size_t)cap * cap, 1);
    bufA = calloc((size_t)cap * NS, sizeof(u64));
    bufB = calloc((size_t)cap * NS, sizeof(u64));
    cov = calloc(NS, sizeof(u64));
    chosen = malloc(sizeof(int) * (dg + 2));
    L0 = malloc(sizeof(int) * cap);
    L1 = malloc(sizeof(int) * cap);
    Q = malloc(sizeof(int) * cap);
    IU = malloc(sizeof(int) * (m0 + 1));
    IV = malloc(sizeof(int) * (m0 + 1));

    n = n0; m = 0;
    for (i = 0; i < m0; i++) {
        int u, w;
        if (scanf("%d %d", &u, &w) != 2) { printf("1 0\n"); return 0; }
        if (u < 0 || u >= n0 || w < 0 || w >= n0 || u == w || AT(u, w)) {
            printf("1 0\n");
            return 0;
        }
        AT(u, w) = 1; AT(w, u) = 1;
        deg[u]++; deg[w]++;
        IU[i] = u; IV[i] = w;
    }
    for (v = 0; v < n; v++) if (deg[v] > dg) { printf("1 0\n"); return 0; }

    /* Two-colour the input; reject if not bipartite. */
    for (v = 0; v < n; v++) col[v] = -1;
    for (v = 0; v < n; v++) {
        int qh = 0, qt = 0;
        if (col[v] >= 0) continue;
        col[v] = 0; Q[qt++] = v;
        while (qh < qt) {
            int u = Q[qh++], w;
            for (w = 0; w < n; w++) {
                if (!AT(u, w)) continue;
                if (col[w] < 0) { col[w] = 1 - col[u]; Q[qt++] = w; }
                else if (col[w] == col[u]) { printf("1 0\n"); return 0; }
            }
        }
    }

    /* Rebuild the edge list with side-0 first. */
    for (i = 0; i < m0; i++) { AT(IU[i], IV[i]) = 0; AT(IV[i], IU[i]) = 0; }
    for (v = 0; v < n; v++) deg[v] = 0;
    m = 0;
    for (i = 0; i < m0; i++) add_edge(IU[i], IV[i]);

    snap_new_dummy:
    init = snap_new();
    tmp = snap_new();
    best = snap_new();
    snap_save(&best);

    c0 = bad_pairs(DM);
    if (c0 != 0) {
        if (!anneal(4000, TEMPER)) {
            /* Input is not valid; print it unchanged so the caller rejects it. */
            printf("%d %d\n", best.n, best.m);
            for (e = 0; e < best.m; e++) printf("%d %d\n", best.U[e], best.V[e]);
            return 0;
        }
        snap_save(&best);
    }
    (void)init;

    t0 = clock();
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        int ok;
        if (el >= tl) break;
        if (m < 2) break;
        snap_save(&tmp);
        if (rndi(100) < 70 && n < cap) {
            if (!add_vertex(rndi(2))) continue;
            ok = anneal(ITERS_ADD, TEMPER);
        } else {
            int k = 1 + rndi(3), t;
            for (t = 0; t < k; t++) apply_switch(rndi(m), rndi(m));
            ok = anneal(ITERS_PERT, TEMPER);
        }
        if (ok) {
            if (n > best.n) snap_save(&best);
        } else {
            snap_restore(&tmp);
        }
    }

    printf("%d %d\n", best.n, best.m);
    for (e = 0; e < best.m; e++) printf("%d %d\n", best.U[e], best.V[e]);
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
    """W(q) for the largest prime power q with q + 1 <= d (q kept small for Python speed)."""
    for q in range(d - 1, 1, -1):
        if q <= 9 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Python helpers for growing a base before the C search.
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


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
            for attempt in range(60):
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


# ----------------------------------------------------------------------------
# Entry point: structured base, then the C engine (vertex addition with greedy
# cover and stealing, annealed switch repair, and plateau perturbation).
# Two rounds, each restarting from the best graph found so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 1.0
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

    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
            consider(n1, e1)

    if D >= 2 and best_n < lib.moore_bound(d, D):
        for r in range(2):
            left = end - time.monotonic()
            if left < 2.0:
                break
            budget = left / (2 - r)
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed * 2 + r, f"{budget:.2f}"],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                break

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
