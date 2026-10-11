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

#define NMAX 1400
#define WMAX ((NMAX + 63) / 64)
#define DMAX 48
#define ITERS 3000

static int dd, DD;
static int n;
static int deg[NMAX];
static int adj[NMAX][DMAX];
static unsigned char A[NMAX][NMAX];
static int col[NMAX];
static uint64_t bufA[NMAX][WMAX];
static uint64_t bufB[NMAX][WMAX];
static uint64_t rs;
static clock_t t0;
static double tlimit;
static int qbuf[NMAX];

static int sN;
static int sDeg[NMAX];
static int sAdj[NMAX][DMAX];
static int sCol[NMAX];
static unsigned char sA[NMAX][NMAX];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int timeup(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC > tlimit; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void del_nb(int u, int v) {
    for (int k = 0; k < deg[u]; k++) {
        if (adj[u][k] == v) {
            adj[u][k] = adj[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}
static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
    A[u][v] = 1;
    A[v][u] = 1;
}
static void del_edge(int u, int v) {
    del_nb(u, v);
    del_nb(v, u);
    A[u][v] = 0;
    A[v][u] = 0;
}

static void shuffle(int *x, int m) {
    for (int i = m - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Number of ordered pairs (v,u) with v != u... returned as unordered bad pairs
   (pairs at distance > DD). Bitset BFS-ball computation. */
static int cost(void) {
    int W = (n + 63) >> 6;
    uint64_t (*cur)[WMAX] = bufA;
    uint64_t (*nxt)[WMAX] = bufB;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) cur[v][w] = 0;
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DD; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *src = cur[adj[v][k]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[WMAX] = cur;
        cur = nxt;
        nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        bad += n - c;
    }
    return (int)(bad / 2);
}

/* Random vertex of the given side with positive degree, or -1. */
static int pick_side(int side) {
    for (int t = 0; t < 40; t++) {
        int v = rndint(n);
        if (col[v] == side && deg[v] > 0) return v;
    }
    int cnt = 0, pick = -1;
    for (int v = 0; v < n; v++) {
        if (col[v] == side && deg[v] > 0) {
            cnt++;
            if (rndint(cnt) == 0) pick = v;
        }
    }
    return pick;
}

/* Propose a bipartite double-edge switch a-b, c-e -> a-e, c-b (a,c side 0). */
static int propose(int *pa, int *pb, int *pc, int *pe) {
    int a = pick_side(0), c = pick_side(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a][rndint(deg[a])];
    int e = adj[c][rndint(deg[c])];
    if (b == e || A[a][e] || A[c][b]) return 0;
    *pa = a; *pb = b; *pc = c; *pe = e;
    return 1;
}
static void apply_sw(int a, int b, int c, int e) {
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
}
static void undo_sw(int a, int b, int c, int e) {
    del_edge(a, e);
    del_edge(c, b);
    add_edge(a, b);
    add_edge(c, e);
}

/* Simulated annealing on switches minimising bad pairs. Returns final cost. */
static int anneal(int iters, double T0, double T1) {
    int cur = cost();
    for (int it = 0; it < iters && cur > 0; it++) {
        if ((it & 63) == 0 && timeup()) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_sw(a, b, c, e);
        int nw = cost();
        int acc = nw <= cur;
        if (!acc) acc = rnd01() < exp(-(double)(nw - cur) / T);
        if (acc) cur = nw;
        else undo_sw(a, b, c, e);
    }
    return cur;
}

/* Cost-preserving random switches: diversifies a valid graph of fixed order. */
static void shuffle_valid(int k) {
    for (int i = 0; i < k; i++) {
        int a, b, c, e;
        if (!propose(&a, &b, &c, &e)) continue;
        apply_sw(a, b, c, e);
        if (cost() != 0) undo_sw(a, b, c, e);
    }
}

/* Randomly fill cross-side deficient pairs (only shortens distances). */
static void fill(void) {
    int L[NMAX], R[NMAX], nl = 0, nr = 0;
    for (int v = 0; v < n; v++) {
        if (deg[v] < dd) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        if (deg[a] >= dd) continue;
        for (int j = 0; j < nr && deg[a] < dd; j++) {
            int b = R[j];
            if (deg[b] < dd && !A[a][b]) add_edge(a, b);
        }
    }
}

/* Append a vertex on the side opposite to `side`, joined to up to dd vertices of `side`.
   Saturated neighbours give up one random edge (their partner becomes deficient). */
static void add_vertex(int side) {
    int old = n;
    int cand[NMAX], cnt = 0;
    for (int u = 0; u < old; u++)
        if (col[u] == side) cand[cnt++] = u;
    shuffle(cand, cnt);
    int chosen[DMAX], nc = 0;
    for (int pass = 0; pass < 2 && nc < dd; pass++) {
        for (int i = 0; i < cnt && nc < dd; i++) {
            int u = cand[i];
            if (pass == 0 && deg[u] >= dd) continue;
            int used = 0;
            for (int k = 0; k < nc; k++)
                if (chosen[k] == u) { used = 1; break; }
            if (!used) chosen[nc++] = u;
        }
    }
    int v = old;
    n = old + 1;
    col[v] = 1 - side;
    deg[v] = 0;
    for (int k = 0; k < nc; k++) {
        int s = chosen[k];
        if (deg[s] >= dd) {
            int t = adj[s][rndint(deg[s])];
            del_edge(s, t);
        }
        add_edge(s, v);
    }
}

static void snap(void) {
    sN = n;
    memcpy(sDeg, deg, sizeof deg);
    memcpy(sAdj, adj, sizeof adj);
    memcpy(sCol, col, sizeof col);
    memcpy(sA, A, sizeof A);
}
static void restore(void) {
    n = sN;
    memcpy(deg, sDeg, sizeof deg);
    memcpy(adj, sAdj, sizeof adj);
    memcpy(col, sCol, sizeof col);
    memcpy(A, sA, sizeof A);
}

static void emit(void) {
    long m = 0;
    for (int v = 0; v < n; v++) m += deg[v];
    m /= 2;
    printf("%d %ld\n", n, m);
    for (int v = 0; v < n; v++)
        for (int k = 0; k < deg[v]; k++)
            if (v < adj[v][k]) printf("%d %d\n", v, adj[v][k]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = strtoull(argv[3], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]);
    t0 = clock();
    if (dd < 1 || dd > DMAX || DD < 2) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    n = 0;
    memset(deg, 0, sizeof deg);
    memset(A, 0, sizeof A);
    int ok = 1;
    if (n0 == 0) {
        n = 2 * dd;
        for (int i = 0; i < dd; i++) {
            col[i] = 0;
            col[dd + i] = 1;
        }
        for (int i = 0; i < dd; i++)
            for (int j = 0; j < dd; j++)
                add_edge(i, dd + j);
    } else {
        if (n0 < 1 || n0 > NMAX - 200) ok = 0;
        n = n0;
        for (int i = 0; i < n; i++) col[i] = -1;
        for (int e = 0; e < m0 && ok; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || A[u][v]
                || deg[u] >= dd || deg[v] >= dd) {
                ok = 0;
                break;
            }
            add_edge(u, v);
        }
        for (int s = 0; s < n && ok; s++) {
            if (col[s] >= 0) continue;
            col[s] = 0;
            int qh = 0, qt = 0;
            qbuf[qt++] = s;
            while (qh < qt && ok) {
                int x = qbuf[qh++];
                for (int k = 0; k < deg[x]; k++) {
                    int y = adj[x][k];
                    if (col[y] < 0) {
                        col[y] = 1 - col[x];
                        qbuf[qt++] = y;
                    } else if (col[y] == col[x]) {
                        ok = 0;
                        break;
                    }
                }
            }
        }
    }
    if (!ok) {
        printf("0 0\n");
        return 0;
    }

    if (cost() != 0) {
        if (anneal(ITERS * 4, 2.0, 0.1) != 0) {
            printf("0 0\n");
            return 0;
        }
    }

    while (!timeup()) {
        if (n >= NMAX - 2) break;
        snap();
        add_vertex(rndint(2));
        fill();
        if (anneal(ITERS, 2.0, 0.1) == 0) continue;   /* accepted: one more vertex */
        restore();
        shuffle_valid(150);
    }
    emit();
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions (from the parent pipeline).
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
# Large-neighbourhood search (kill, repair, regrow).
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
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
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
# C stage: switch-based vertex insertion with bitset distance costs.
# ----------------------------------------------------------------------------

def _c_stage(d, D, n, edges, seed, deadline):
    """Run the C engine from (n, edges) until `deadline` (monotonic). Returns (n, edges) or None."""
    budget = deadline - time.monotonic()
    if budget < 2:
        return None
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(n, edges), timeout=budget + 4)
        cn, ce = lib.parse_graph_text(text)
        if cn > n and lib.is_valid(cn, ce, d, D):
            return cn, ce
    except Exception:
        return None
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.1 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    # Randomized twin-duplication pipelines from the structured base.
    if D >= 2:
        trial_end = start + 0.2 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Kill-repair-regrow search from the best valid graph found so far.
    if D >= 2 and time.monotonic() < start + 0.4 * time_limit:
        _lns(best_n, best_e, d, D, start + 0.3 * time_limit, rng, consider)

    # Python add-and-repair, kept as a safety net.
    py_end = start + 0.45 * time_limit
    if D >= 2 and time.monotonic() < py_end:
        _repair(d, D, best_n, best_e, py_end, rng, consider)

    # C stage: anneal-based vertex insertion from the best valid graph.
    if D >= 2 and best_n < lib.moore_bound(d, D):
        c_deadline = start + 0.85 * time_limit
        res = _c_stage(d, D, best_n, best_e, seed, c_deadline)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
