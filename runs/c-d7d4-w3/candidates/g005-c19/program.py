import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine. Starts from a valid graph and repeatedly tries to insert a
# new vertex (wired to d opposite-side vertices, stealing slots when needed),
# then repairs the diameter by annealing over degree-preserving bipartite
# double-edge swaps. Plateau walks keep validity at the current size.
# Every stored state has cost 0 (all pairs within distance D), so the output
# is valid whenever the input was valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NMAX 2048
#define DMAX 40
#define WMAX 32

typedef struct {
    int n;
    int col[NMAX];
    int deg[NMAX];
    int adj[NMAX][DMAX];
} State;

static State CUR, WORK, BEST;
static int DD, DIAM;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t RX[NMAX][WMAX], RY[NMAX][WMAX];
static int CAND[NMAX], LIST0[NMAX], LISTL[NMAX], LISTR[NMAX];

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndi(int m) { return (int)(rnd() % (uint64_t)m); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered pairs at distance > DIAM (unreachable counts). */
static int cost(const State *s) {
    int n = s->n, nw = (n + 63) / 64;
    uint64_t (*X)[WMAX] = RX, (*Y)[WMAX] = RY;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < nw; w++) X[v][w] = 0;
        X[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int st = 0; st < DIAM; st++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < nw; w++) Y[v][w] = X[v][w];
            for (int i = 0; i < s->deg[v]; i++) {
                int u = s->adj[v][i];
                for (int w = 0; w < nw; w++) Y[v][w] |= X[u][w];
            }
        }
        uint64_t (*t)[WMAX] = X; X = Y; Y = t;
    }
    long long tot = 0;
    for (int v = 0; v < n; v++)
        for (int w = 0; w < nw; w++)
            tot += popc(X[v][w]);
    return (int)(((long long)n * n - tot) / 2);
}

static int has_edge(const State *s, int a, int b) {
    for (int i = 0; i < s->deg[a]; i++)
        if (s->adj[a][i] == b) return 1;
    return 0;
}

static void add_edge(State *s, int a, int b) {
    s->adj[a][s->deg[a]++] = b;
    s->adj[b][s->deg[b]++] = a;
}

static void rem_one(State *s, int a, int b) {
    for (int i = 0; i < s->deg[a]; i++) {
        if (s->adj[a][i] == b) {
            s->adj[a][i] = s->adj[a][--s->deg[a]];
            return;
        }
    }
}

static void rem_edge(State *s, int a, int b) {
    rem_one(s, a, b);
    rem_one(s, b, a);
}

static void shuffle_int(int *a, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndi(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

/* Greedily add cross-side edges between deficient vertices (only lowers cost). */
static void fill(State *s) {
    int nl = 0, nr = 0;
    for (int v = 0; v < s->n; v++) {
        if (s->deg[v] < DD) {
            if (s->col[v] == 0) LISTL[nl++] = v;
            else LISTR[nr++] = v;
        }
    }
    shuffle_int(LISTL, nl);
    shuffle_int(LISTR, nr);
    for (int i = 0; i < nl; i++) {
        int a = LISTL[i];
        for (int j = 0; j < nr && s->deg[a] < DD; j++) {
            int b = LISTR[j];
            if (s->deg[b] >= DD || has_edge(s, a, b)) continue;
            add_edge(s, a, b);
        }
    }
}

/* Add vertex of colour c wired to up to DD opposite-side vertices. */
static void insert_vertex(State *s, int c) {
    int v = s->n++;
    s->col[v] = c;
    s->deg[v] = 0;
    int nc = 0;
    for (int u = 0; u < v; u++)
        if (s->col[u] != c) CAND[nc++] = u;
    shuffle_int(CAND, nc);
    int k = 0;
    for (int i = 0; i < nc && k < DD; i++, k++) {
        int b = CAND[i];
        if (s->deg[b] >= DD) {
            int x = s->adj[b][rndi(s->deg[b])];
            rem_edge(s, b, x);
        }
        add_edge(s, v, b);
    }
}

static int collect_side0(const State *s) {
    int nl0 = 0;
    for (int v = 0; v < s->n; v++)
        if (s->col[v] == 0) LIST0[nl0++] = v;
    return nl0;
}

/* Annealing over double-edge swaps until cost 0. Returns final cost. */
static int anneal(State *s, int iters, double T) {
    int nl0 = collect_side0(s);
    if (nl0 < 2) return cost(s);
    int cur = cost(s);
    for (int it = 0; it < iters && cur > 0; it++) {
        if (it % 50 == 49) {
            fill(s);
            cur = cost(s);
            if (cur == 0) break;
        }
        int a = LIST0[rndi(nl0)];
        if (s->deg[a] == 0) continue;
        int b = s->adj[a][rndi(s->deg[a])];
        int c = LIST0[rndi(nl0)];
        if (c == a || s->deg[c] == 0) continue;
        int e = s->adj[c][rndi(s->deg[c])];
        if (has_edge(s, a, e) || has_edge(s, c, b)) continue;
        rem_edge(s, a, b); rem_edge(s, c, e);
        add_edge(s, a, e); add_edge(s, c, b);
        int nw = cost(s);
        int delta = nw - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nw;
        } else {
            rem_edge(s, a, e); rem_edge(s, c, b);
            add_edge(s, a, b); add_edge(s, c, e);
        }
    }
    return cur;
}

/* Zero-cost plateau walk: swaps are kept only if the graph stays valid. */
static void walk(State *s, int iters) {
    int nl0 = collect_side0(s);
    if (nl0 < 2) return;
    for (int it = 0; it < iters; it++) {
        int a = LIST0[rndi(nl0)];
        if (s->deg[a] == 0) continue;
        int b = s->adj[a][rndi(s->deg[a])];
        int c = LIST0[rndi(nl0)];
        if (c == a || s->deg[c] == 0) continue;
        int e = s->adj[c][rndi(s->deg[c])];
        if (has_edge(s, a, e) || has_edge(s, c, b)) continue;
        rem_edge(s, a, b); rem_edge(s, c, e);
        add_edge(s, a, e); add_edge(s, c, b);
        if (cost(s) != 0) {
            rem_edge(s, a, e); rem_edge(s, c, b);
            add_edge(s, a, b); add_edge(s, c, e);
        }
    }
}

static int two_colour(State *s) {
    for (int v = 0; v < s->n; v++) s->col[v] = -1;
    static int stack[NMAX];
    for (int st = 0; st < s->n; st++) {
        if (s->col[st] != -1) continue;
        s->col[st] = 0;
        int sp = 0;
        stack[sp++] = st;
        while (sp > 0) {
            int u = stack[--sp];
            for (int i = 0; i < s->deg[u]; i++) {
                int w = s->adj[u][i];
                if (s->col[w] == -1) {
                    s->col[w] = 1 - s->col[u];
                    stack[sp++] = w;
                }
            }
        }
    }
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (s->col[s->adj[v][i]] == s->col[v]) return 0;
    return 1;
}

static void emit(const State *s) {
    int m = 0;
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (s->adj[v][i] > v) m++;
    printf("%d %d\n", s->n, m);
    for (int v = 0; v < s->n; v++)
        for (int i = 0; i < s->deg[v]; i++)
            if (s->adj[v][i] > v) printf("%d %d\n", v, s->adj[v][i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs ^= seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    clock_t t0 = clock();

    if (DD < 1 || DD > DMAX || DIAM < 2) { printf("0 0\n"); return 0; }

    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n < 1 || n > NMAX || m < 0 || m > NMAX * DMAX / 2) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (m + 1));
    int *ev = malloc(sizeof(int) * (m + 1));
    if (!eu || !ev) { printf("0 0\n"); return 0; }
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    memset(&CUR, 0, sizeof(CUR));
    CUR.n = n;
    for (int i = 0; i < m; i++) {
        int a = eu[i], b = ev[i];
        if (a < 0 || a >= n || b < 0 || b >= n || a == b) { printf("0 0\n"); return 0; }
        if (CUR.deg[a] >= DD || CUR.deg[b] >= DD || has_edge(&CUR, a, b)) { printf("0 0\n"); return 0; }
        add_edge(&CUR, a, b);
    }
    if (!two_colour(&CUR) || cost(&CUR) != 0) { printf("0 0\n"); return 0; }

    BEST = CUR;
    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= tl) break;
        if (CUR.n >= NMAX - 2) break;
        if (rndi(4) == 0) {
            WORK = CUR;
            insert_vertex(&WORK, rndi(2));
            fill(&WORK);
            if (anneal(&WORK, 300, 0.4) == 0) {
                CUR = WORK;
                if (CUR.n > BEST.n) BEST = CUR;
            }
        } else {
            walk(&CUR, 200);
        }
    }
    emit(&BEST);
    free(eu);
    free(ev);
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

    Degree is q + 1, diameter is 4, and the order is 2(q+1)(q^2+1).
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


def _raw_big(d, D):
    """A dense structured graph whose degree is at least d (later thinned)."""
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
    """Greedily join deficient opposite-side vertices in random order. Keeps validity."""
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
# Twin duplication: a non-adjacent twin keeps distances and bipartiteness.
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
    """Delete the worst vertices in batches until the diameter bound holds. Returns (n, edges) or None."""
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
    """One thinning trial from the dense raw graph. Returns (n, edges) valid, or None."""
    e = _reduce_degree(raw_n, raw_e, d, rng)
    r = _delete_to_valid(raw_n, e, d, D, rng, deadline)
    if r is None:
        return None
    n2, e2 = r
    return _grow(n2, e2, d, D, deadline, rng)


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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


def _local_kill(n, edges, k, rng):
    """Vertex set of size <= k grown by BFS from a random vertex."""
    adj = _to_sets(n, edges)
    s = rng.randrange(n)
    seen = [s]
    seen_set = {s}
    i = 0
    while len(seen) < k and i < len(seen):
        nbrs = list(adj[seen[i]])
        rng.shuffle(nbrs)
        for u in nbrs:
            if len(seen) >= k:
                break
            if u not in seen_set:
                seen_set.add(u)
                seen.append(u)
        i += 1
    return seen_set


def _lns(n, edges, d, D, deadline, rng, consider):
    """Kill-repair-regrow large-neighbourhood search from a valid graph."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4, 6))
        if k >= cur_n:
            break
        if rng.random() < 0.5:
            kill = set(rng.sample(range(cur_n), k))
        else:
            kill = _local_kill(cur_n, cur_e, k, rng)
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


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Python pipeline (fallback and C starting point).
# ----------------------------------------------------------------------------

def _python_build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Phase A: structured small base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
            consider(n1, e1)
    if D >= 2:
        trial_end = at(0.20)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)
        _lns(best_n, best_e, d, D, at(0.40), rng, consider)

    # Phase B: thinned dense structured graph.
    if D >= 2 and time.monotonic() < at(0.55):
        raw = _raw_big(d, D)
        if raw is not None:
            rn, re = raw
            while time.monotonic() < at(0.55):
                r = _deletion_trial(d, D, rn, re, rng, at(0.55))
                if r is None:
                    break
                consider(*r)

    # Phase C: LNS from the best valid graph.
    if D >= 2 and time.monotonic() < at(0.75):
        _lns(best_n, best_e, d, D, at(0.75), rng, consider)

    # Phase D: prune and regrow.
    if D >= 2 and time.monotonic() < at(1.0):
        _prune_regrow(best_n, best_e, d, D, at(1.0), rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver: Python construction and search first, then the C engine grows the
# best valid graph. Every returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()

    py_n, py_e = _python_build(d, D, seed, 0.40 * time_limit)
    if not lib.is_valid(py_n, py_e, d, D):
        py_n, py_e = lib.haar_graph(d, range(d))
    best_n, best_e = py_n, list(py_e)

    if D < 2 or d < 2 or best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    remaining = time_limit - (time.monotonic() - t0)
    budget = remaining * 0.80 - 1.0
    if budget < 1.0:
        return best_n, best_e

    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                        stdin_graph=(best_n, best_e),
                        timeout=remaining * 0.93 - 0.5)
        n, e = lib.parse_graph_text(out)
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
    except Exception:
        pass

    return best_n, list(best_e)
