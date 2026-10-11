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

typedef uint64_t u64;

#define ITERS 2000

static int DEG, DIAM, n, cap, WS, bn;
static int *adj, *dg, *col;
static int *badj, *bdg, *bcol;
static u64 *bufA, *bufB, *cov;
static u64 rs;
static double T_END;
static int la, lb, lc, le;

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static u64 rnd(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int k) { return (int)(rnd() % (u64)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < dg[a]; i++)
        if (adj[a * DEG + i] == b) return 1;
    return 0;
}

static void drop_nb(int a, int b) {
    int *p = adj + (size_t)a * DEG;
    for (int i = 0; i < dg[a]; i++)
        if (p[i] == b) {
            p[i] = p[dg[a] - 1];
            dg[a]--;
            return;
        }
}

static void add_edge(int a, int b) {
    adj[a * DEG + dg[a]++] = b;
    adj[b * DEG + dg[b]++] = a;
}

static void del_edge(int a, int b) {
    drop_nb(a, b);
    drop_nb(b, a);
}

/* Bitsets of radius-r balls. Returns whichever buffer holds the result. */
static u64 *balls(int r, u64 *X, u64 *Y) {
    int Wn = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        u64 *x = X + (size_t)v * WS;
        memset(x, 0, sizeof(u64) * Wn);
        x[v >> 6] |= 1ULL << (v & 63);
    }
    for (int s = 0; s < r; s++) {
        for (int v = 0; v < n; v++) {
            u64 *y = Y + (size_t)v * WS;
            u64 *x = X + (size_t)v * WS;
            memcpy(y, x, sizeof(u64) * Wn);
            for (int i = 0; i < dg[v]; i++) {
                const u64 *z = X + (size_t)adj[v * DEG + i] * WS;
                for (int w = 0; w < Wn; w++) y[w] |= z[w];
            }
        }
        u64 *t = X;
        X = Y;
        Y = t;
    }
    return X;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long cost(void) {
    u64 *R = balls(DIAM, bufA, bufB);
    int Wn = (n + 63) >> 6;
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const u64 *x = R + (size_t)v * WS;
        int cnt = 0;
        for (int w = 0; w < Wn; w++) cnt += pc64(x[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static int rand_side(int side) {
    for (;;) {
        int v = rndint(n);
        if (col[v] == side) return v;
    }
}

/* Degree-preserving bipartite double-edge switch. */
static int try_switch(void) {
    int a = rand_side(0), c = rand_side(0);
    if (a == c || dg[a] == 0 || dg[c] == 0) return 0;
    int b = adj[a * DEG + rndint(dg[a])];
    int e = adj[c * DEG + rndint(dg[c])];
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    la = a; lb = b; lc = c; le = e;
    return 1;
}

static void undo_switch(void) {
    del_edge(la, le);
    del_edge(lc, lb);
    add_edge(la, lb);
    add_edge(lc, le);
}

static void shuffle_int(int *a, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Join deficient opposite-colour vertices that are not yet adjacent. */
static void fill(void) {
    int *L = malloc(sizeof(int) * n), *R = malloc(sizeof(int) * n);
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (dg[v] >= DEG) continue;
        if (col[v] == 0) L[nl++] = v;
        else R[nr++] = v;
    }
    shuffle_int(L, nl);
    shuffle_int(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && dg[a] < DEG; j++) {
            int b = R[j];
            if (dg[b] < DEG && !has_edge(a, b)) add_edge(a, b);
        }
    }
    free(L);
    free(R);
}

/* Append a vertex whose neighbourhood greedily covers the radius-(DIAM-1) balls. */
static int add_vertex(void) {
    if (n >= cap) return 0;
    int Wn = (n + 63) >> 6;
    int nc = rndint(2), oc = 1 - nc;
    u64 *R = balls(DIAM - 1, bufA, bufB);
    for (int w = 0; w < Wn; w++) cov[w] = 0;
    char *used = calloc(n, 1);
    int chosen[64];
    int nch = 0;
    for (int k = 0; k < DEG; k++) {
        int best = -1;
        double bs = -1.0;
        for (int s = 0; s < n; s++) {
            if (col[s] != oc || used[s]) continue;
            int g = 0;
            const u64 *x = R + (size_t)s * WS;
            for (int w = 0; w < Wn; w++) g += pc64(x[w] & ~cov[w]);
            double sc = g + 0.5 * rnd01();
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const u64 *x = R + (size_t)best * WS;
        for (int w = 0; w < Wn; w++) cov[w] |= x[w];
    }
    free(used);
    int v = n++;
    col[v] = nc;
    dg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (dg[s] >= DEG) {
            int t = adj[s * DEG + rndint(dg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
    return 1;
}

static long anneal(long cur, int iters, double T0, double T1) {
    double T = T0;
    double f = pow(T1 / T0, 1.0 / iters);
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && now() > T_END) break;
        T *= f;
        if (!try_switch()) continue;
        long nc = cost();
        if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) cur = nc;
        else undo_switch();
    }
    return cur;
}

static void save_base(void) {
    bn = n;
    memcpy(badj, adj, sizeof(int) * (size_t)n * DEG);
    memcpy(bdg, dg, sizeof(int) * n);
    memcpy(bcol, col, sizeof(int) * n);
}

static void restore_base(void) {
    n = bn;
    memcpy(adj, badj, sizeof(int) * (size_t)bn * DEG);
    memcpy(dg, bdg, sizeof(int) * bn);
    memcpy(col, bcol, sizeof(int) * bn);
}

static void perturb(int k) {
    int done = 0;
    for (int t = 0; t < 50 * k && done < k; t++)
        if (try_switch()) done++;
}

static void print_base(void) {
    long m = 0;
    for (int v = 0; v < bn; v++) m += bdg[v];
    m /= 2;
    printf("%d %ld\n", bn, m);
    for (int v = 0; v < bn; v++)
        for (int i = 0; i < bdg[v]; i++) {
            int w = badj[v * DEG + i];
            if (v < w) printf("%d %d\n", v, w);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    T_END = now() + tl;

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 <= 0 || DEG < 1 || DEG > 64 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * m0), *ev = malloc(sizeof(int) * m0);
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2 || eu[i] < 0 || ev[i] < 0 ||
            eu[i] >= n0 || ev[i] >= n0) {
            printf("0 0\n");
            return 0;
        }
    }

    cap = n0 + 4096;
    WS = (cap + 63) >> 6;
    adj = calloc((size_t)cap * DEG, sizeof(int));
    dg = calloc(cap, sizeof(int));
    col = calloc(cap, sizeof(int));
    badj = calloc((size_t)cap * DEG, sizeof(int));
    bdg = calloc(cap, sizeof(int));
    bcol = calloc(cap, sizeof(int));
    bufA = calloc((size_t)cap * WS, sizeof(u64));
    bufB = calloc((size_t)cap * WS, sizeof(u64));
    cov = calloc(WS, sizeof(u64));
    n = n0;

    for (int i = 0; i < m0; i++) {
        int u = eu[i], v = ev[i];
        if (u == v || dg[u] >= DEG || dg[v] >= DEG || has_edge(u, v)) {
            printf("0 0\n");
            return 0;
        }
        add_edge(u, v);
    }

    /* Two-colour the graph; reject if it is not bipartite. */
    int *queue = malloc(sizeof(int) * n);
    for (int v = 0; v < n; v++) col[v] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < dg[u]; i++) {
                int w = adj[u * DEG + i];
                if (col[w] < 0) {
                    col[w] = 1 - col[u];
                    queue[qt++] = w;
                }
            }
        }
    }
    free(queue);
    for (int i = 0; i < m0; i++)
        if (col[eu[i]] == col[ev[i]]) {
            printf("0 0\n");
            return 0;
        }
    if (cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    save_base();

    while (now() < T_END) {
        restore_base();
        if (rnd01() < 0.2) perturb(3);
        else add_vertex();
        fill();
        long c = cost();
        c = anneal(c, ITERS, 1.0, 0.05);
        if (c == 0) save_base();
    }
    print_base();
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
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add twins in random order while neighbours have spare degree."""
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
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
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
# C stage: simulated annealing over degree-preserving switches, with
# greedy vertex insertion and repair. Only valid graphs are kept.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, n, edges, budget):
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=(n, edges), timeout=budget + 5.0)
    return lib.parse_graph_text(out)


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
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            grow_end = start + 0.15 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the current best graph.
    if D >= 2:
        trial_end = start + 0.22 * time_limit
        base_n, base_e = best_n, list(best_e)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing / vertex-insertion search from the best valid graph so far.
    c_end = start + 0.85 * time_limit
    if D >= 2 and time.monotonic() < c_end - 3.0:
        budget = c_end - time.monotonic() - 1.0
        try:
            n5, e5 = _c_search(d, D, seed, best_n, best_e, budget)
            consider(n5, e5)
        except (RuntimeError, ValueError, OSError):
            pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
