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

#define MAXN 4096
#define MAXW 64

typedef uint64_t u64;

static int DEG, DIAM, N, M;
static int *ea, *eb;
static int col[MAXN], deg[MAXN];
static unsigned char *A;
static u64 *BX, *BY;
static u64 rs = 88172645463325252ULL;
static int *sa, *sb, sM, sN;
static int scol[MAXN], sdeg[MAXN];
static int chosen[MAXN], used[MAXN], Lw[MAXN], Lf[MAXN], Rt[MAXN];

static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (u64)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void setA(int a, int b, unsigned char v) {
    A[(size_t)a * MAXN + b] = v;
    A[(size_t)b * MAXN + a] = v;
}

/* Bitmask balls of radius r in the current graph; returns pointer into BX or BY. */
static u64 *balls(int r) {
    int W = (N + 63) / 64;
    u64 *cur = BX, *nxt = BY;
    memset(cur, 0, sizeof(u64) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < r; s++) {
        memcpy(nxt, cur, sizeof(u64) * (size_t)N * W);
        for (int i = 0; i < M; i++) {
            int a = ea[i], b = eb[i];
            u64 *na = nxt + (size_t)a * W, *nb = nxt + (size_t)b * W;
            const u64 *ca = cur + (size_t)a * W, *cb = cur + (size_t)b * W;
            for (int w = 0; w < W; w++) {
                na[w] |= cb[w];
                nb[w] |= ca[w];
            }
        }
        u64 *t = cur; cur = nxt; nxt = t;
    }
    return cur;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long cost(void) {
    int W = (N + 63) / 64;
    u64 *b = balls(DIAM);
    long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(b[(size_t)v * W + w]);
        tot += N - c;
    }
    return tot / 2;
}

static void add_edge(int u, int v) {
    int a = (col[u] == 0) ? u : v;
    int b = (a == u) ? v : u;
    ea[M] = a;
    eb[M] = b;
    M++;
    setA(a, b, 1);
    deg[u]++;
    deg[v]++;
}

static void del_edge(int i) {
    int a = ea[i], b = eb[i];
    setA(a, b, 0);
    deg[a]--;
    deg[b]--;
    M--;
    ea[i] = ea[M];
    eb[i] = eb[M];
}

/* Bipartite double-edge switches minimising bad pairs. Returns final cost (0 = valid). */
static long anneal(long iters, clock_t lim) {
    long cur = cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > lim) break;
        if (M < 2) break;
        int i = rndi(M), j = rndi(M);
        if (i == j) continue;
        int a = ea[i], b = eb[i], c = ea[j], e = eb[j];
        if (a == c || b == e) continue;
        if (A[(size_t)a * MAXN + e] || A[(size_t)c * MAXN + b]) continue;
        setA(a, b, 0);
        setA(c, e, 0);
        setA(a, e, 1);
        setA(c, b, 1);
        ea[i] = a; eb[i] = e;
        ea[j] = c; eb[j] = b;
        long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndu() < 0.1)) {
            cur = nw;
        } else {
            setA(a, e, 0);
            setA(c, b, 0);
            setA(a, b, 1);
            setA(c, e, 1);
            ea[i] = a; eb[i] = b;
            ea[j] = c; eb[j] = e;
        }
    }
    return cur;
}

static void snap(void) {
    memcpy(sa, ea, sizeof(int) * M);
    memcpy(sb, eb, sizeof(int) * M);
    sM = M;
    sN = N;
    memcpy(scol, col, sizeof(int) * N);
    memcpy(sdeg, deg, sizeof(int) * N);
}

static void restore(void) {
    for (int i = 0; i < M; i++) setA(ea[i], eb[i], 0);
    M = sM;
    N = sN;
    memcpy(ea, sa, sizeof(int) * M);
    memcpy(eb, sb, sizeof(int) * M);
    for (int i = 0; i < M; i++) setA(ea[i], eb[i], 1);
    memcpy(col, scol, sizeof(int) * N);
    memcpy(deg, sdeg, sizeof(int) * N);
}

/* Add a vertex on side t, joined to a greedy cover (radius DIAM-1) chosen from the other side. */
static void add_vertex(int t) {
    int n0 = N;
    int W0 = (n0 + 63) / 64;
    u64 *Bd = balls(DIAM - 1);
    u64 cov[MAXW];
    memset(cov, 0, sizeof cov);
    int nl = 0;
    for (int s = 0; s < n0; s++) {
        used[s] = 0;
        if (col[s] == 1 - t) Lw[nl++] = s;
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = Lw[i]; Lw[i] = Lw[j]; Lw[j] = tmp;
    }
    int nch = 0;
    for (int k = 0; k < DEG; k++) {
        int best = -1, bg = -1, ties = 0;
        for (int q = 0; q < nl; q++) {
            int s = Lw[q];
            if (used[s]) continue;
            int g = 0;
            const u64 *bs = Bd + (size_t)s * W0;
            for (int w = 0; w < W0; w++) g += pc64(bs[w] & ~cov[w]);
            if (g > bg) {
                bg = g; best = s; ties = 1;
            } else if (g == bg) {
                ties++;
                if (rndi(ties) == 0) best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        const u64 *bs = Bd + (size_t)best * W0;
        for (int w = 0; w < W0; w++) cov[w] |= bs[w];
    }

    int v = N;
    N++;
    col[v] = t;
    deg[v] = 0;
    for (int k = 0; k < nch; k++) {
        int s = chosen[k];
        if (deg[s] >= DEG) {
            int cnt = 0, pick = -1;
            for (int i = 0; i < M; i++) {
                if (ea[i] == s || eb[i] == s) {
                    cnt++;
                    if (rndi(cnt) == 0) pick = i;
                }
            }
            if (pick >= 0) del_edge(pick);
        }
        if (deg[s] < DEG) add_edge(s, v);
    }
}

/* Join deficient opposite-side vertices in random order (only shortens distances). */
static void fill(void) {
    int nl = 0, nr = 0;
    for (int v = 0; v < N; v++) {
        if (deg[v] < DEG) {
            if (col[v] == 0) Lf[nl++] = v;
            else Rt[nr++] = v;
        }
    }
    for (int i = nl - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = Lf[i]; Lf[i] = Lf[j]; Lf[j] = tmp;
    }
    for (int i = nr - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int tmp = Rt[i]; Rt[i] = Rt[j]; Rt[j] = tmp;
    }
    for (int i = 0; i < nl; i++) {
        int a = Lf[i];
        for (int j = 0; j < nr; j++) {
            if (deg[a] >= DEG) break;
            int b = Rt[j];
            if (deg[b] < DEG && !A[(size_t)a * MAXN + b]) add_edge(a, b);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs ^= (u64)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 1;
    if (rs == 0) rs = 1;
    double budget = atof(argv[4]);
    clock_t lim = clock() + (clock_t)(budget * CLOCKS_PER_SEC);

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n >= MAXN - 2 || DEG < 1 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    size_t cape = (size_t)MAXN * (size_t)DEG + 16;
    A = calloc((size_t)MAXN * MAXN, 1);
    BX = calloc((size_t)MAXN * MAXW, sizeof(u64));
    BY = calloc((size_t)MAXN * MAXW, sizeof(u64));
    ea = malloc(sizeof(int) * cape);
    eb = malloc(sizeof(int) * cape);
    sa = malloc(sizeof(int) * cape);
    sb = malloc(sizeof(int) * cape);
    int *tu = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int *tv = malloc(sizeof(int) * (size_t)(m > 0 ? m : 1));
    int nt = 0;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (A[(size_t)u * MAXN + v]) continue;
        if (deg[u] >= DEG || deg[v] >= DEG) continue;
        setA(u, v, 1);
        deg[u]++;
        deg[v]++;
        tu[nt] = u;
        tv[nt] = v;
        nt++;
    }

    /* Two-colour the start graph; reject anything that is not bipartite. */
    for (int v = 0; v < N; v++) col[v] = -1;
    int *st = malloc(sizeof(int) * (size_t)N);
    int bad = 0;
    for (int s = 0; s < N && !bad; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        st[sp++] = s;
        while (sp) {
            int u = st[--sp];
            for (int v = 0; v < N; v++) {
                if (!A[(size_t)u * MAXN + v]) continue;
                if (col[v] == -1) {
                    col[v] = 1 - col[u];
                    st[sp++] = v;
                } else if (col[v] == col[u]) {
                    bad = 1;
                }
            }
        }
    }
    if (bad) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild oriented edge list (side 0 first) and degrees. */
    memset(deg, 0, sizeof deg);
    M = 0;
    for (int i = 0; i < nt; i++) add_edge(tu[i], tv[i]);

    snap();
    while (clock() < lim) {
        if (N >= MAXN - 2) break;
        snap();
        int side = rndi(2);
        add_vertex(side);
        fill();
        long c = anneal(3000, lim);
        if (c != 0) restore();
    }

    printf("%d %d\n", N, M);
    for (int i = 0; i < M; i++) printf("%d %d\n", ea[i], eb[i]);
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


def _extend_cover(n, edges, d, D, deadline, rng=None):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Adding cross-side edges keeps the graph bipartite and degrees <= d, and can only
    shorten distances, so a valid graph stays valid.
    """
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
# Twin duplication.
#
# A vertex v' with N(v') = N(v), v' not adjacent to v, is a "twin" of v. In any
# graph, non-adjacent twins are at the same distance from every other vertex,
# and at distance 2 from each other. So duplicating a vertex never breaks the
# diameter bound (for D >= 2), keeps the graph bipartite (v' is on v's side),
# and needs only spare degree on the neighbours of v.
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    deadline = start + 0.88 * tl
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
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.2 * tl
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.3 * tl
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # C annealing stage: add vertices one at a time, repairing by bipartite switches.
    if D >= 2 and best_n >= 2:
        budget = deadline - time.monotonic() - 2.5
        if budget >= 1.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                stdin_graph=(best_n, best_e), timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
