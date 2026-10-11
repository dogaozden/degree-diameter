import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealed vertex growth. Starting from a valid bipartite graph, it
# repeatedly adds a vertex joined to spare-degree or switched vertices on the
# opposite side, repairs the diameter with bipartite double-edge switches
# (cost = number of pairs farther than D, computed with bitsets), and keeps the
# largest valid graph seen. Restarts from the best graph after repeated failures.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXD 16

static int d, D, n, W;
static int deg[MAXN], col[MAXN];
static int nb[MAXN][MAXD];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static unsigned char pct[256];
static uint64_t rs;

static int bestN;
static int bestDeg[MAXN], bestNb[MAXN][MAXD], bestCol[MAXN];
static int snapN, snapDeg[MAXN], snapNb[MAXN][MAXD], snapCol[MAXN];
static int side0buf[MAXN];

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }

static int pc64(uint64_t x) {
    return pct[x & 255] + pct[(x >> 8) & 255] + pct[(x >> 16) & 255] + pct[(x >> 24) & 255]
         + pct[(x >> 32) & 255] + pct[(x >> 40) & 255] + pct[(x >> 48) & 255] + pct[(x >> 56) & 255];
}

/* Number of unordered pairs at distance > D (unreachable pairs count). */
static long long cost(void) {
    uint64_t (*cur)[MAXW] = bufA, (*nxt)[MAXW] = bufB;
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = nb[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= cur[u][w];
            }
        }
        uint64_t (*t)[MAXW] = cur; cur = nxt; nxt = t;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (nb[a][i] == b) return 1;
    return 0;
}

static void rem_one(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (nb[a][i] == b) { nb[a][i] = nb[a][--deg[a]]; return; }
    }
}

static void rem_edge(int a, int b) { rem_one(a, b); rem_one(b, a); }

static void add_edge(int a, int b) {
    nb[a][deg[a]++] = b;
    nb[b][deg[b]++] = a;
}

static void build_kdd(void) {
    n = 2 * d;
    for (int i = 0; i < n; i++) { deg[i] = 0; col[i] = (i < d) ? 0 : 1; }
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) add_edge(i, d + j);
}

/* Bipartite double-edge switches minimising cost. Returns 1 if cost reaches 0. */
static int anneal(int iters, clock_t endc) {
    long long cur = cost();
    int k = 0;
    for (int v = 0; v < n; v++) if (col[v] == 0) side0buf[k++] = v;
    if (k < 2) return cur == 0;
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 31) == 0 && clock() > endc) break;
        int a = side0buf[rndint(k)];
        int c = side0buf[rndint(k)];
        if (a == c || deg[a] == 0 || deg[c] == 0) continue;
        int b = nb[a][rndint(deg[a])];
        int e = nb[c][rndint(deg[c])];
        if (has_edge(a, e) || has_edge(c, b)) continue;
        rem_edge(a, b); rem_edge(c, e);
        add_edge(a, e); add_edge(c, b);
        long long nw = cost();
        if (nw <= cur || (nw == cur + 1 && rndint(10) == 0)) {
            cur = nw;
        } else {
            rem_edge(a, e); rem_edge(c, b);
            add_edge(a, b); add_edge(c, e);
        }
    }
    return cur == 0;
}

/* Add one vertex on a random side, joined to d opposite-side vertices
   (switching out an edge at saturated ones), then fill deficient cross pairs. */
static int grow_once(void) {
    if (n + 2 >= MAXN) return 0;
    int s = rndint(2);
    int v = n;
    n++;
    deg[v] = 0;
    col[v] = s;
    int cand[MAXN], k = 0;
    for (int x = 0; x < v; x++) if (col[x] == 1 - s) cand[k++] = x;
    for (int i = k - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    int picked = 0;
    for (int pass = 0; pass < 2 && picked < d; pass++) {
        for (int i = 0; i < k && picked < d; i++) {
            int x = cand[i];
            if (has_edge(x, v)) continue;
            if (pass == 0 && deg[x] >= d) continue;
            if (pass == 1 && deg[x] < d) continue;
            if (deg[x] >= d) {
                int p = nb[x][rndint(deg[x])];
                rem_edge(x, p);
            }
            add_edge(x, v);
            picked++;
        }
    }
    if (picked == 0) { n--; return 0; }
    int L[MAXN], R[MAXN], nl = 0, nr = 0;
    for (int x = 0; x < n; x++) {
        if (deg[x] < d) {
            if (col[x] == 0) L[nl++] = x; else R[nr++] = x;
        }
    }
    int tries = 4 * (nl + nr) + 8;
    for (int t = 0; t < tries && nl > 0 && nr > 0; t++) {
        int a = L[rndint(nl)], b = R[rndint(nr)];
        if (deg[a] < d && deg[b] < d && !has_edge(a, b)) add_edge(a, b);
    }
    return 1;
}

static void snap_save(void) {
    snapN = n;
    memcpy(snapDeg, deg, sizeof(deg));
    memcpy(snapNb, nb, sizeof(nb));
    memcpy(snapCol, col, sizeof(col));
}

static void snap_load(void) {
    n = snapN;
    memcpy(deg, snapDeg, sizeof(deg));
    memcpy(nb, snapNb, sizeof(nb));
    memcpy(col, snapCol, sizeof(col));
}

static void best_save(void) {
    bestN = n;
    memcpy(bestDeg, deg, sizeof(deg));
    memcpy(bestNb, nb, sizeof(nb));
    memcpy(bestCol, col, sizeof(col));
}

static void restore_best(void) {
    n = bestN;
    memcpy(deg, bestDeg, sizeof(deg));
    memcpy(nb, bestNb, sizeof(nb));
    memcpy(col, bestCol, sizeof(col));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    for (int i = 0; i < 256; i++) {
        int c = 0, x = i;
        while (x) { c += x & 1; x >>= 1; }
        pct[i] = (unsigned char)c;
    }
    clock_t endc = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N = 0, M = 0;
    if (scanf("%d %d", &N, &M) != 2) { N = 0; M = 0; }
    int ok = (N > 0 && N < MAXN - 2 && M >= 0);
    if (ok) {
        n = N;
        for (int i = 0; i < n; i++) deg[i] = 0;
        for (int i = 0; i < M && ok; i++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
    }
    if (ok) {
        int stack[MAXN], sp;
        for (int i = 0; i < n; i++) col[i] = -1;
        for (int s = 0; s < n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0; sp = 0; stack[sp++] = s;
            while (sp > 0 && ok) {
                int x = stack[--sp];
                for (int i = 0; i < deg[x]; i++) {
                    int y = nb[x][i];
                    if (col[y] == -1) { col[y] = 1 - col[x]; stack[sp++] = y; }
                    else if (col[y] == col[x]) { ok = 0; break; }
                }
            }
        }
    }
    if (!ok) build_kdd();
    if (cost() != 0) {
        if (!anneal(20000, endc)) build_kdd();
    }
    best_save();

    int fails = 0;
    while (clock() < endc) {
        snap_save();
        if (!grow_once()) {
            snap_load();
            if (++fails >= 60) { restore_best(); fails = 0; }
            continue;
        }
        if (anneal(3000, endc)) {
            if (n > bestN) best_save();
            fails = 0;
        } else {
            snap_load();
            if (++fails >= 60) { restore_best(); fails = 0; }
        }
    }

    int m = 0;
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (bestNb[v][i] > v) m++;
    printf("%d %d\n", bestN, m);
    for (int v = 0; v < bestN; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (bestNb[v][i] > v) printf("%d %d\n", v, bestNb[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions.
# ----------------------------------------------------------------------------

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
        if q <= 9 and lib.is_prime_power(q):
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list.

    Cross-side edges keep the graph bipartite and degrees <= d, and can only
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
# Twin duplication: a non-adjacent twin of v (same neighbourhood) keeps the
# diameter bound for D >= 2, stays on v's side, and needs only spare degree
# on the neighbours of v.
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
# Random voltage lifts of small d-regular bipartite base multigraphs.
# Vertices u*m+g with u < k are side 0; u >= k are side 1.
# ----------------------------------------------------------------------------

def _random_lift(k, m, d, rng):
    """Random Z_m lift of a d-regular bipartite multigraph on k + k base vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append((i, k + perm[i], rng.randrange(m)))
    return lib.voltage_lift(2 * k, darts, m)


def _lift_search(d, D, deadline, rng, best_n, consider):
    """Search random voltage lifts slightly above best_n, repair them, then grow."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        if best_n >= moore:
            return
        k = rng.choice((1, 1, 2, 3))
        target = min(moore, best_n + rng.randint(1, 12))
        m = -(-target // (2 * k))
        if 2 * k * m > moore:
            m = moore // (2 * k)
        if m < 2 or 2 * k * m <= best_n:
            continue
        n, e = _random_lift(k, m, d, rng)
        adj = _to_sets(n, e)
        color = [0 if v < k * m else 1 for v in range(n)]
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(n) for v in adj[u] if u < v]
        consider(n, e3)
        n4, e4 = _grow(n, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n = n4


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow), anchored to its best graph.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


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
        # Switch a-b, c-e into a-e, c-b (a, c on side 0; b, e on side 1).
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
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        # Accept sideways and slightly downward moves to drift across the plateau.
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            # Drifted too far below the best graph: return to it.
            cur_n, cur_e = best_n, list(best_e)


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing with annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Native annealed growth through the C engine.
# ----------------------------------------------------------------------------

def _c_refine(d, D, seed, budget, graph, consider):
    """Run the C annealed-growth engine from `graph` for about `budget` CPU seconds."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"], stdin_graph=graph,
                    timeout=budget + 20.0)
    n, e = lib.parse_graph_text(out)
    consider(n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    py_end = start + 0.5 * time_limit
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

    try:
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
                grow_end = start + 0.12 * time_limit
                n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
                consider(n1, e1)

        # Randomized twin-duplication pipelines from the structured base.
        if D >= 2:
            trial_end = start + 0.2 * time_limit
            while time.monotonic() < trial_end:
                n, e = _trial(base_n, base_e, d, D, rng, trial_end)
                consider(n, e)

        # Random voltage lifts of small bipartite base multigraphs, repaired and grown.
        if D >= 2 and time.monotonic() < py_end:
            lift_end = start + 0.28 * time_limit
            _lift_search(d, D, lift_end, rng, best_n, consider)

        # Kill-repair-regrow search from the best valid graph found so far.
        if D >= 2 and time.monotonic() < py_end:
            lns_end = start + 0.4 * time_limit
            _lns(best_n, best_e, d, D, lns_end, rng, consider)

        # Bold stage: repeated add-and-repair from the largest valid graph found so far.
        if D >= 2 and time.monotonic() < py_end:
            _repair(d, D, best_n, best_e, py_end, rng, consider)
    except Exception:
        pass

    # Native stage: annealed vertex growth in C from the best valid graph.
    if D >= 2:
        c_end = start + 0.92 * time_limit
        budget = c_end - time.monotonic() - 2.0
        if budget >= 1.0:
            try:
                _c_refine(d, D, seed, budget, (best_n, list(best_e)), consider)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
