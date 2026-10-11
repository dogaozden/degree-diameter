"""Bitset-annealing vertex growth on top of the twin/cover/pair pipeline.

The Python pipeline (projective planes, generalized quadrangles, twins, cover and
pair extension, non-cyclic voltage lifts) builds a valid start graph. A C engine
then grows it one vertex pair at a time. Each pair is connected greedily, then
annealed with two move types that keep max degree <= d and bipartiteness:
  * 2-switch: (a,b),(c,e) -> (a,e),(c,b), which keeps every degree;
  * transfer: move an edge end from a saturated vertex x to a deficient vertex v.
Cost = number of vertex pairs at distance > D, computed with 64-bit bitset balls.
A growth attempt that reaches cost 0 becomes the new snapshot. Otherwise the
snapshot is restored. Python re-verifies the output with lib.is_valid and keeps
the parent's graph if anything fails.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define DMAX 40
#define OPMAX 4096
#define SNAPMAX (MAXN * DMAX)
#define ITERS 1500
#define MAXFAIL 200

static int N, dd, DD, W;
static unsigned char A[MAXN][MAXN];
static int adjl[MAXN][DMAX];
static int deg[MAXN];
static int col[MAXN];
static uint64_t Bx[MAXN][MAXW], By[MAXN][MAXW];
static unsigned long long rs;
static double tlim;

typedef struct { int type, u, v; } Op;
static Op oplog[OPMAX];
static int oplen = 0, logging = 0;

static int snapN = 0, snapM = 0;
static int snapU[SNAPMAX], snapV[SNAPMAX], snapC[MAXN];

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void raw_add(int u, int v) {
    A[u][v] = 1; A[v][u] = 1;
    adjl[u][deg[u]++] = v;
    adjl[v][deg[v]++] = u;
}

static void raw_adj_remove(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (adjl[u][i] == v) {
            adjl[u][i] = adjl[u][deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void raw_del(int u, int v) {
    A[u][v] = 0; A[v][u] = 0;
    raw_adj_remove(u, v);
    raw_adj_remove(v, u);
}

static void add_edge(int u, int v) {
    raw_add(u, v);
    if (logging && oplen < OPMAX) {
        oplog[oplen].type = 1; oplog[oplen].u = u; oplog[oplen].v = v; oplen++;
    }
}

static void del_edge(int u, int v) {
    raw_del(u, v);
    if (logging && oplen < OPMAX) {
        oplog[oplen].type = 0; oplog[oplen].u = u; oplog[oplen].v = v; oplen++;
    }
}

static void undo(void) {
    logging = 0;
    for (int i = oplen - 1; i >= 0; i--) {
        if (oplog[i].type == 1) raw_del(oplog[i].u, oplog[i].v);
        else raw_add(oplog[i].u, oplog[i].v);
    }
    oplen = 0;
}

/* Number of unordered pairs at distance > DD (unreachable counts as bad). */
static int bad_pairs(void) {
    int n = N;
    W = (n + 63) >> 6;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) Bx[v][w] = 0;
        Bx[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    uint64_t (*cur)[MAXW] = Bx, (*nxt)[MAXW] = By;
    for (int it = 0; it < DD; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = cur[v][w];
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *src = cur[adjl[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= src[w];
            }
        }
        uint64_t (*t)[MAXW] = cur;
        cur = nxt;
        nxt = t;
    }
    long long miss = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(cur[v][w]);
        miss += n - c;
    }
    return (int)(miss / 2);
}

/* Greedily join a to opposite-side deficient vertices. */
static void fill_vertex(int a) {
    if (deg[a] >= dd) return;
    int n = N;
    int start = rndint(n);
    for (int k = 0; k < n && deg[a] < dd; k++) {
        int b = start + k;
        if (b >= n) b -= n;
        if (b != a && col[b] != col[a] && deg[b] < dd && !A[a][b])
            add_edge(a, b);
    }
}

static void fill_all(void) {
    int n = N;
    int *perm = malloc(sizeof(int) * (size_t)(n > 0 ? n : 1));
    for (int i = 0; i < n; i++) perm[i] = i;
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
    }
    for (int i = 0; i < n; i++) fill_vertex(perm[i]);
    free(perm);
}

/* Add a new adjacent pair (v side 0, w side 1), then fill both. */
static int grow_pair(void) {
    if (N + 2 > MAXN - 2) return 0;
    int v = N, w = N + 1;
    N += 2;
    col[v] = 0; col[w] = 1;
    deg[v] = 0; deg[w] = 0;
    raw_add(v, w);
    fill_vertex(v);
    fill_vertex(w);
    return 1;
}

static void take_snapshot(void) {
    snapN = N;
    snapM = 0;
    for (int v = 0; v < N; v++) {
        snapC[v] = col[v];
        for (int i = 0; i < deg[v]; i++) {
            int u = adjl[v][i];
            if (u > v) {
                snapU[snapM] = v; snapV[snapM] = u; snapM++;
            }
        }
    }
}

static void restore_snapshot(void) {
    for (int i = 0; i < N; i++) memset(A[i], 0, (size_t)N);
    for (int v = 0; v < N; v++) deg[v] = 0;
    N = snapN;
    for (int v = 0; v < N; v++) col[v] = snapC[v];
    for (int i = 0; i < snapM; i++) raw_add(snapU[i], snapV[i]);
    oplen = 0;
    logging = 0;
}

static int rand_edge(int *a, int *b) {
    for (int t = 0; t < 50; t++) {
        int p = rndint(N);
        if (deg[p] == 0) continue;
        int q = adjl[p][rndint(deg[p])];
        if (col[p] == 0) { *a = p; *b = q; }
        else { *a = q; *b = p; }
        return 1;
    }
    return 0;
}

/* 2-switch: (a,b),(c,e) -> (a,e),(c,b). Degrees are unchanged. */
static int swap2(void) {
    int a, b, c, e;
    if (!rand_edge(&a, &b)) return 0;
    if (!rand_edge(&c, &e)) return 0;
    if (a == c || b == e) return 0;
    if (A[a][e] || A[c][b]) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    return 1;
}

/* Transfer: a saturated vertex x gives an edge end to a deficient vertex v. */
static int transfer(void) {
    int v = -1;
    for (int t = 0; t < 60 && v < 0; t++) {
        int p = rndint(N);
        if (deg[p] < dd) v = p;
    }
    if (v < 0) return 0;
    int b = -1;
    for (int t = 0; t < 60 && b < 0; t++) {
        int p = rndint(N);
        if (col[p] != col[v] && deg[p] >= dd && !A[v][p]) b = p;
    }
    if (b < 0) return 0;
    if (deg[b] == 0) return 0;
    int x = adjl[b][rndint(deg[b])];
    if (x == v) return 0;
    del_edge(x, b);
    add_edge(v, b);
    fill_vertex(x);
    return 1;
}

static int propose(void) {
    if (rndint(2)) return swap2();
    return transfer();
}

static int anneal(int iters, double T0, double T1, int cost) {
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 31) == 0 && now() > tlim) break;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        oplen = 0;
        logging = 1;
        if (!propose()) {
            logging = 0;
            oplen = 0;
            continue;
        }
        int nc = bad_pairs();
        int delta = nc - cost;
        logging = 0;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cost = nc;
        } else {
            undo();
        }
        oplen = 0;
    }
    return cost;
}

static void print_snapshot(void) {
    printf("%d %d\n", snapN, snapM);
    for (int i = 0; i < snapM; i++) printf("%d %d\n", snapU[i], snapV[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((unsigned long long)atoll(argv[3]) * 0xBF58476D1CE4E5B9ULL);
    if (rs == 0) rs = 1;
    tlim = atof(argv[4]);

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 64 || m < 0) {
        printf("0 0\n");
        return 0;
    }
    int *eu = malloc(sizeof(int) * (size_t)(m + 1));
    int *ev = malloc(sizeof(int) * (size_t)(m + 1));
    for (int i = 0; i < m; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }

    #define PRINT_INPUT() do { printf("%d %d\n", n, m); \
        for (int _i = 0; _i < m; _i++) printf("%d %d\n", eu[_i], ev[_i]); } while (0)

    if (dd < 2 || dd > DMAX - 4 || DD < 1) { PRINT_INPUT(); return 0; }

    /* Load the start graph and check it. */
    N = n;
    for (int v = 0; v < n; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < m && ok; i++) {
        int u = eu[i], v = ev[i];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) { ok = 0; break; }
        if (A[u][v] || deg[u] >= dd || deg[v] >= dd) { ok = 0; break; }
        raw_add(u, v);
    }
    if (ok) {
        for (int v = 0; v < n; v++) col[v] = -1;
        int *stack = malloc(sizeof(int) * (size_t)n);
        for (int s = 0; s < n && ok; s++) {
            if (col[s] != -1) continue;
            col[s] = 0;
            int sp = 0;
            stack[sp++] = s;
            while (sp > 0 && ok) {
                int u = stack[--sp];
                for (int i = 0; i < deg[u]; i++) {
                    int v = adjl[u][i];
                    if (col[v] == -1) { col[v] = 1 - col[u]; stack[sp++] = v; }
                    else if (col[v] == col[u]) { ok = 0; break; }
                }
            }
        }
        free(stack);
    }
    if (!ok || bad_pairs() != 0) { PRINT_INPUT(); return 0; }

    fill_all();
    take_snapshot();

    int fails = 0;
    while (now() < tlim && fails < MAXFAIL) {
        if (!grow_pair()) break;
        int cost = bad_pairs();
        cost = anneal(ITERS, 1.5, 0.08, cost);
        if (cost == 0) {
            fill_all();   /* adding edges never increases distances */
            take_snapshot();
            fails = 0;
        } else {
            restore_snapshot();
            fails++;
        }
    }
    print_snapshot();
    return 0;
}
'''


def _python_build_placeholder_marker():
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
# Twin extension. A twin v of x (same side, N(v) = N(x)) keeps all old distances,
# has dist(v, x) = 2, and preserves bipartiteness. It needs one spare degree on
# each neighbour of x. Twins are added greedily in random passes until none remain.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
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


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; the diameter is preserved."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


# ----------------------------------------------------------------------------
# Cover-based vertex extension.
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices."""
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


# ----------------------------------------------------------------------------
# Rarity-weighted set cover.
# ----------------------------------------------------------------------------

def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball (as 0/1 vector over n vertices) of idx[r]."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows of sub."""
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None
        w = np.where(uncovered > 0, 1.0 / np.maximum(cnt, 1.0), 0.0).astype(np.float32)
        gain = sub @ w
        gain[~avail_b] = -1.0
        best = float(gain.max())
        if best <= 0:
            return None
        if randomize:
            thr = best * (0.9 if rng.random() < 0.3 else 1.0)
            opts = np.flatnonzero((gain >= thr) & avail_b)
            i = int(opts[rng.randrange(len(opts))])
        else:
            i = int(np.argmax(gain))
        chosen.append(cands[i])
        avail_b[i] = False
        uncovered[sub[i] > 0] = 0.0
    return chosen


def _weighted_cover_search(cands, ball, n, d, rng, tries, deadline):
    """Try several weighted covers (first deterministic, then randomised)."""
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


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
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _weighted_cover_search(cands, ball, n, d, rng, 15, deadline)
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


# ----------------------------------------------------------------------------
# Pair extension. Add two adjacent vertices v (side 0) and w (side 1) at once.
# ----------------------------------------------------------------------------

def _extend_pairs(n, edges, d, D, deadline, rng):
    """Greedily add (v, w) pairs whose neighbour sets cover the old vertices for both."""
    if D < 3 or d < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    fails = 0
    while fails < 3 and time.monotonic() < deadline:
        r1 = _balls_radius(n, adj, D - 1)
        r2 = _balls_radius(n, adj, D - 2)
        full = (1 << n) - 1
        Uv, Uw = full, full
        Sv, Sw, used = [], [], set()
        pool1 = [s for s in range(n) if color[s] == 1 and deg[s] < d]
        pool0 = [s for s in range(n) if color[s] == 0 and deg[s] < d]
        ok = True
        while Uv or Uw:
            if time.monotonic() >= deadline:
                ok = False
                break
            best_int, best_key, pick, pside = 0, -1.0, None, None
            if len(Sv) < d - 1:
                for s in pool1:
                    if s in used:
                        continue
                    sc = (r1[s] & Uv).bit_count() + (r2[s] & Uw).bit_count()
                    key = sc + 0.99 * rng.random()
                    if sc > 0 and key > best_key:
                        best_int, best_key, pick, pside = sc, key, s, 1
            if len(Sw) < d - 1:
                for t in pool0:
                    if t in used:
                        continue
                    sc = (r1[t] & Uw).bit_count() + (r2[t] & Uv).bit_count()
                    key = sc + 0.99 * rng.random()
                    if sc > 0 and key > best_key:
                        best_int, best_key, pick, pside = sc, key, t, 0
            if pick is None:
                ok = False
                break
            used.add(pick)
            if pside == 1:
                Sv.append(pick)
                Uv &= ~r1[pick]
                Uw &= ~r2[pick]
            else:
                Sw.append(pick)
                Uw &= ~r1[pick]
                Uv &= ~r2[pick]
        if not ok:
            fails += 1
            continue
        fails = 0
        v, w = n, n + 1
        n += 2
        color.extend([0, 1])
        adj.extend([[], []])
        deg.extend([0, 0])
        for s in Sv:
            edges.append((s, v))
            adj[s].append(v)
            adj[v].append(s)
            deg[s] += 1
            deg[v] += 1
        for t in Sw:
            edges.append((t, w))
            adj[t].append(w)
            adj[w].append(t)
            deg[t] += 1
            deg[w] += 1
        edges.append((v, w))
        adj[v].append(w)
        adj[w].append(v)
        deg[v] += 1
        deg[w] += 1
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then pair extensions, then saturate edges."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        n3, e3 = _extend_pairs(n2, e2, d, D, deadline, rng)
        grew = n3 != cur_n
        cur_n = n3
        cur_e = _saturate_edges(cur_n, e3, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover/pair growth until none adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over NON-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
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
# Haar and cyclic-lift families, kept for D = 3 and as a secondary family.
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
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
    """Hill-climb Z_m voltages on a random d-regular bipartite base with k+k vertices."""
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


def _python_build(d, D, seed, time_limit):
    """The Python construction and search pipeline (returns a valid (n, edges))."""
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    ext_deadline = start + 0.5 * time_limit
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

    # D >= 3: projective planes for the few largest prime powers q with q + 1 <= d.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, ext_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: generalized quadrangle W(q), grown by an iterated search.
    pipe_end = start + 0.88 * time_limit
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            while time.monotonic() < pipe_end:
                if cur is None or rng.random() < 0.2:
                    src_n, src_e = gq[0], gq[1]
                else:
                    frac = rng.uniform(0.05, 0.3)
                    src_n, src_e = _remove_twins(cur[0], cur[1], frac, rng)
                    src_e = _saturate_edges(src_n, src_e, d, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, pipe_end, rng)
                consider(pn, pe)
                if cur is None or pn >= cur[0]:
                    cur = (pn, pe)

    # Main search. For D >= 4 the non-cyclic group-lift family dominates.
    group_p = 0.85 if D >= 4 else 0.3
    haar_p = 0.35 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0

    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = best_n // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
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
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
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
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                ladder[k] = m + 1
            else:
                ladder[k] = m

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


def build(d, D, seed, time_limit):
    # Phase 1: Python construction and search (about half the budget).
    base = _python_build(d, D, seed, 0.5 * time_limit)
    if D < 3 or d < 3:
        return base

    # Phase 2: C bitset annealing that adds vertex pairs to the base graph.
    c_budget = 0.4 * time_limit
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                        stdin_graph=base, timeout=c_budget + 0.2 * time_limit)
        n, e = lib.parse_graph_text(out)
        if n > base[0] and lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    return base
