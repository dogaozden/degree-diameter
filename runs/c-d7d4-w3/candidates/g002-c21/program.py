import itertools
import math
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

#define MAXN 1100
#define MAXD 24
#define MAXW ((MAXN + 63) / 64)
#define STAGE 20000

static int d_, D_, n, n0;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static int side0[MAXN];
static uint64_t ballA[MAXN][MAXW];
static uint64_t ballB[MAXN][MAXW];
static int W;

static int bestN = 0;
static int bestDeg[MAXN];
static int bestAdj[MAXN][MAXD];
static int bestCol[MAXN];

static uint64_t rs = 1;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static double urand(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int irand(int k) { return (int)(rnd() % (uint64_t)k); }

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) return 1;
    return 0;
}
static void add_edge(int a, int b) {
    adj[a][deg[a]++] = b;
    adj[b][deg[b]++] = a;
}
static void drop(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a][i] == b) {
            adj[a][i] = adj[a][--deg[a]];
            return;
        }
}
static void remove_edge(int a, int b) {
    drop(a, b);
    drop(b, a);
}

static void balls(int r) {
    W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) ballA[v][w] = 0;
        ballA[v][v >> 6] |= (uint64_t)1 << (v & 63);
    }
    for (int it = 0; it < r; it++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) ballB[v][w] = ballA[v][w];
            for (int k = 0; k < deg[v]; k++) {
                int u = adj[v][k];
                for (int w = 0; w < W; w++) ballB[v][w] |= ballA[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) ballA[v][w] = ballB[v][w];
    }
}

static long long cost(void) {
    balls(D_);
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        int p = 0;
        for (int w = 0; w < W; w++) p += pop64(ballA[v][w]);
        bad += n - p;
    }
    return bad / 2;
}

static void rebuild_sides(void) {
    n0 = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == 0) side0[n0++] = v;
}

static void shuffle(int *x, int k) {
    for (int i = k - 1; i > 0; i--) {
        int j = irand(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

static void saturate(void) {
    static int L[MAXN], R[MAXN];
    int nl = 0, nr = 0;
    for (int v = 0; v < n; v++)
        if (deg[v] < d_) {
            if (col[v] == 0) L[nl++] = v;
            else R[nr++] = v;
        }
    shuffle(L, nl);
    shuffle(R, nr);
    for (int i = 0; i < nl; i++) {
        int a = L[i];
        for (int j = 0; j < nr && deg[a] < d_; j++) {
            int b = R[j];
            if (deg[b] < d_ && !has_edge(a, b)) add_edge(a, b);
        }
    }
}

static void grow_vertex(void) {
    int c = irand(2), t = 1 - c;
    balls(D_ - 1);
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    static int used[MAXN];
    for (int v = 0; v < n; v++) used[v] = 0;
    int chosen[MAXD], nch = 0;
    for (int k = 0; k < d_; k++) {
        int best = -1;
        double bs = -1e18;
        for (int s = 0; s < n; s++) {
            if (col[s] != t || used[s]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += pop64(ballA[s][w] & ~cov[w]);
            double sc = g + (urand() < 0.3 ? 2.5 * urand() : 0.5 * urand());
            if (sc > bs) {
                bs = sc;
                best = s;
            }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= ballA[best][w];
    }
    int v = n++;
    col[v] = c;
    deg[v] = 0;
    for (int i = 0; i < nch; i++) {
        int s = chosen[i];
        if (deg[s] >= d_) {
            int tt = adj[s][irand(deg[s])];
            remove_edge(s, tt);
        }
        add_edge(s, v);
    }
}

static void save_best(void) {
    bestN = n;
    for (int v = 0; v < n; v++) {
        bestDeg[v] = deg[v];
        bestCol[v] = col[v];
        for (int k = 0; k < deg[v]; k++) bestAdj[v][k] = adj[v][k];
    }
}

static void restore_best(void) {
    n = bestN;
    for (int v = 0; v < n; v++) {
        deg[v] = bestDeg[v];
        col[v] = bestCol[v];
        for (int k = 0; k < deg[v]; k++) adj[v][k] = bestAdj[v][k];
    }
    rebuild_sides();
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long sd = strtoul(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)sd * 0xBF58476D1CE4E5B9ULL + 1ULL);
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double t0 = (double)clock() / CLOCKS_PER_SEC;

    int N = 0, M = 0;
    if (scanf("%d %d", &N, &M) != 2) {
        N = 0;
        M = 0;
    }
    if (d_ < 1 || d_ > MAXD || D_ < 1 || N <= 0 || N >= MAXN - 64 || M < 0) {
        printf("1 0\n");
        return 0;
    }
    n = N;
    for (int v = 0; v < n; v++) deg[v] = 0;
    int ok = 1;
    for (int i = 0; i < M && ok; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) {
            ok = 0;
            break;
        }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) {
            ok = 0;
            break;
        }
        if (deg[u] >= d_ || deg[v] >= d_ || has_edge(u, v)) {
            ok = 0;
            break;
        }
        add_edge(u, v);
    }
    for (int v = 0; v < n; v++) col[v] = -1;
    static int q[MAXN];
    for (int s = 0; s < n && ok; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        q[qt++] = s;
        while (qh < qt && ok) {
            int x = q[qh++];
            for (int k = 0; k < deg[x]; k++) {
                int y = adj[x][k];
                if (col[y] < 0) {
                    col[y] = 1 - col[x];
                    q[qt++] = y;
                } else if (col[y] == col[x]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    if (!ok) {
        printf("1 0\n");
        return 0;
    }

    rebuild_sides();
    long long cur = cost();
    if (cur == 0) save_best();
    int stage = 0;
    double T = 0.1 * pow(10.0, urand() * 1.3);
    long long iter = 0;
    while (1) {
        if ((iter & 7) == 0) {
            double el = (double)clock() / CLOCKS_PER_SEC - t0;
            if (el > tl) break;
        }
        iter++;
        if (cur == 0) {
            if (n > bestN) save_best();
            if (n + 2 >= MAXN) break;
            grow_vertex();
            rebuild_sides();
            saturate();
            cur = cost();
            stage = 0;
            T = 0.1 * pow(10.0, urand() * 1.3);
            continue;
        }
        if (n0 < 2) break;
        stage++;
        int a = side0[irand(n0)];
        int c = side0[irand(n0)];
        if (a != c && deg[a] > 0 && deg[c] > 0) {
            int b = adj[a][irand(deg[a])];
            int e = adj[c][irand(deg[c])];
            if (!has_edge(a, e) && !has_edge(c, b)) {
                remove_edge(a, b);
                remove_edge(c, e);
                add_edge(a, e);
                add_edge(c, b);
                long long nw = cost();
                if (nw <= cur || urand() < exp(-(double)(nw - cur) / T)) {
                    cur = nw;
                } else {
                    remove_edge(a, e);
                    remove_edge(c, b);
                    add_edge(a, b);
                    add_edge(c, e);
                }
            }
        }
        if (stage > STAGE) {
            if (bestN > 0) {
                restore_best();
                cur = cost();
            }
            stage = 0;
            T = 0.1 * pow(10.0, urand() * 1.3);
        }
    }
    if (bestN == 0) {
        printf("1 0\n");
        return 0;
    }
    int total = 0;
    for (int v = 0; v < bestN; v++) total += bestDeg[v];
    total /= 2;
    printf("%d %d\n", bestN, total);
    for (int v = 0; v < bestN; v++)
        for (int k = 0; k < bestDeg[v]; k++)
            if (v < bestAdj[v][k]) printf("%d %d\n", v, bestAdj[v][k]);
    return 0;
}
'''


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
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
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


def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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
# Lifts and C search.
# ----------------------------------------------------------------------------

def _lift2(n, edges, rng):
    """Random Z_2 lift: edge (u, v) becomes (u, i)-(v, i XOR s). Degrees and bipartiteness are kept.

    The result may violate the diameter bound; the C engine repairs it by annealing.
    """
    out = []
    for u, v in edges:
        s = rng.randrange(2)
        for i in range(2):
            out.append((u + n * i, v + n * (i ^ s)))
    return 2 * n, out


def _c_search(d, D, n, edges, seed, budget):
    """Run the C annealing engine from a start graph (degree/bipartite valid). Returns (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                    stdin_graph=(n, edges), timeout=budget + 15.0)
    return lib.parse_graph_text(out)


# ----------------------------------------------------------------------------
# Driver.
#   A  structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown
#   B  randomized twin/grow trials
#   C  C engine (switch annealing with bad-pair cost, grow-when-zero) from the best graph
#   D  C engine from a random 2-lift of the best graph (repair search)
# Every candidate passes lib.is_valid before it is kept; K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    def left():
        return at(1.0) - time.monotonic()

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

    # Phase A: structured base.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, at(0.08), rng)
            consider(n1, e1)

    # Phase B: randomized twin trials.
    if D >= 2:
        trial_end = at(0.15)
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    # Phases C and D: C engine. Skip when the Moore bound is already reached.
    if D >= 2 and time_limit >= 8 and best_n < lib.moore_bound(d, D):
        rem = left()
        if rem > 6:
            try:
                n2, e2 = _c_search(d, D, best_n, best_e, seed, 0.6 * rem)
                consider(n2, e2)
            except Exception:
                pass
        rem = left()
        if rem > 6:
            try:
                ln, le = _lift2(best_n, best_e, rng)
                n3, e3 = _c_search(d, D, ln, le, seed + 1, rem - 5)
                consider(n3, e3)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
