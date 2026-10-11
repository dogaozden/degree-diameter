import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: fixed-order tabu search with min-conflict 2-switch moves.
#
# State: a bipartite graph with max degree DEG and n vertices. Cost = number of
# unordered pairs at distance > DIAM. A move picks a vertex v with bad pairs,
# a non-neighbour x on the other side, a neighbour z of v and a neighbour y of x,
# and replaces v-z, x-y by v-x, z-y (all degrees preserved). Among NCAND random
# candidates the best non-tabu move is applied, even if it worsens the cost.
# Removed edges become tabu for re-insertion for a short tenure.
# Whenever cost is 0 the graph is saved and one new vertex is grown in.
# Stalls trigger a random perturbation.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <limits.h>

#define MAXN 2600
#define WMAX ((MAXN + 63) / 64)
#define DEGMAX 32
#define NCAND 8
#define STALL 600

static int DEG, DIAM;
static int nv;
static int adjv[MAXN][DEGMAX];
static int deg[MAXN];
static int col[MAXN];
static int badv[MAXN];
static int bestAdj[MAXN][DEGMAX];
static int bestDeg[MAXN];
static int bestNv;
static int have_valid = 0;
static uint64_t RA[MAXN * WMAX];
static uint64_t RB[MAXN * WMAX];
static unsigned int tabu[MAXN * MAXN];
static uint64_t rs = 1;
static int defA[MAXN], defB[MAXN], stk[MAXN];

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static long long eval_cost(void) {
    int W = (nv + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)nv * (size_t)W);
    for (int v = 0; v < nv; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < nv; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        badv[v] = nv - cnt;
        bad += badv[v];
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adjv[a][i] == b) {
            adjv[a][i] = adjv[a][deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void raw_add(int a, int b) {
    adjv[a][deg[a]++] = b;
    adjv[b][deg[b]++] = a;
}

static void raw_remove(int a, int b) {
    del_half(a, b);
    del_half(b, a);
}

static void shuffle_int(int *x, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd(i + 1);
        int t = x[i];
        x[i] = x[j];
        x[j] = t;
    }
}

/* Pick x (other side, non-adjacent), z in N(v), y in N(x), with z-y absent. */
static int sample_move(int v, int *ox, int *oz, int *oy) {
    if (deg[v] == 0) return 0;
    for (int t = 0; t < 60; t++) {
        int x = rnd(nv);
        if (x == v || col[x] == col[v] || deg[x] == 0 || has_edge(v, x)) continue;
        int z = adjv[v][rnd(deg[v])];
        int y = adjv[x][rnd(deg[x])];
        if (has_edge(z, y)) continue;
        *ox = x;
        *oz = z;
        *oy = y;
        return 1;
    }
    return 0;
}

/* Remove v-z, x-y; add v-x, z-y. Degrees are preserved. */
static void make_move(int v, int x, int z, int y) {
    raw_remove(v, z);
    raw_remove(x, y);
    raw_add(v, x);
    raw_add(z, y);
}

static void undo_move(int v, int x, int z, int y) {
    raw_remove(v, x);
    raw_remove(z, y);
    raw_add(v, z);
    raw_add(x, y);
}

static int pick_bad(void) {
    int cnt = 0, v = -1;
    for (int u = 0; u < nv; u++) {
        if (badv[u] > 0) {
            cnt++;
            if (rnd(cnt) == 0) v = u;
        }
    }
    return v;
}

/* Add edges between deficient opposite-side vertices. Never increases cost. */
static int saturate(void) {
    int nd0 = 0, nd1 = 0, added = 0;
    for (int u = 0; u < nv; u++) {
        if (deg[u] < DEG) {
            if (col[u] == 0) defA[nd0++] = u;
            else defB[nd1++] = u;
        }
    }
    for (int i = 0; i < nd0; i++) {
        int a = defA[i];
        for (int j = 0; j < nd1 && deg[a] < DEG; j++) {
            int b = defB[j];
            if (deg[b] < DEG && !has_edge(a, b)) {
                raw_add(a, b);
                added = 1;
            }
        }
    }
    return added;
}

static void grow(void) {
    int c = rnd(2);
    int v = nv++;
    col[v] = c;
    deg[v] = 0;
    int nd = 0, nf = 0;
    for (int w = 0; w < v; w++) {
        if (col[w] != 1 - c) continue;
        if (deg[w] < DEG) defA[nd++] = w;
        else defB[nf++] = w;
    }
    shuffle_int(defA, nd);
    shuffle_int(defB, nf);
    int k = 0;
    for (int i = 0; i < nd && k < DEG; i++) {
        raw_add(v, defA[i]);
        k++;
    }
    for (int i = 0; i < nf && k < DEG; i++) {
        int w = defB[i];
        int x = adjv[w][rnd(deg[w])];
        raw_remove(w, x);
        raw_add(v, w);
        k++;
    }
}

static void save_best(void) {
    memcpy(bestAdj, adjv, sizeof adjv);
    memcpy(bestDeg, deg, sizeof deg);
    bestNv = nv;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();
    if (DEG < 1 || DEG > DEGMAX || DIAM < 1 || tl <= 0) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0 || n > MAXN - 300) {
        printf("0 0\n");
        return 0;
    }
    nv = n;
    for (int i = 0; i < nv; i++) { deg[i] = 0; col[i] = -1; }
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= nv || v >= nv || u == v) continue;
        if (deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) continue;
        raw_add(u, v);
    }

    for (int s = 0; s < nv; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int sp = 0;
        stk[sp++] = s;
        while (sp > 0) {
            int u = stk[--sp];
            for (int i = 0; i < deg[u]; i++) {
                int w = adjv[u][i];
                if (col[w] == -1) {
                    col[w] = 1 - col[u];
                    stk[sp++] = w;
                }
            }
        }
    }

    long long cur = eval_cost();
    save_best();
    have_valid = (cur == 0);
    long long runBest = cur;
    long stall = 0;
    unsigned int iter = 1;
    double t0 = (double)clock() / CLOCKS_PER_SEC;

    while (1) {
        double el = (double)clock() / CLOCKS_PER_SEC - t0;
        if (el >= tl) break;

        if (cur == 0) {
            if (!have_valid || nv > bestNv) {
                save_best();
                have_valid = 1;
            }
            if (nv + 1 >= MAXN - 1) break;
            grow();
            cur = eval_cost();
            runBest = cur;
            stall = 0;
            continue;
        }

        if (saturate()) {
            cur = eval_cost();
            if (cur < runBest) { runBest = cur; stall = 0; }
            continue;
        }

        int v = -1;
        for (int t = 0; t < 20; t++) {
            int u = pick_bad();
            if (u >= 0 && deg[u] > 0) { v = u; break; }
        }
        if (v < 0) {
            stall++;
        } else {
            int bx = -1, bz = -1, by = -1;
            long long bv = LLONG_MAX;
            for (int k = 0; k < NCAND; k++) {
                int x, z, y;
                if (!sample_move(v, &x, &z, &y)) continue;
                int tb = (tabu[(size_t)v * MAXN + x] > iter) ||
                         (tabu[(size_t)z * MAXN + y] > iter);
                make_move(v, x, z, y);
                long long c2 = eval_cost();
                undo_move(v, x, z, y);
                if (tb && c2 >= runBest) continue;
                if (c2 < bv || (c2 == bv && rnd(2) == 0)) {
                    bv = c2;
                    bx = x;
                    bz = z;
                    by = y;
                }
            }
            if (bx < 0) {
                stall++;
            } else {
                make_move(v, bx, bz, by);
                unsigned int ten = (unsigned int)(8 + rnd(12));
                tabu[(size_t)v * MAXN + bz] = iter + ten;
                tabu[(size_t)bz * MAXN + v] = iter + ten;
                tabu[(size_t)bx * MAXN + by] = iter + ten;
                tabu[(size_t)by * MAXN + bx] = iter + ten;
                cur = eval_cost();
                if (cur < runBest) { runBest = cur; stall = 0; }
                else stall++;
            }
        }
        iter++;

        if (stall > STALL) {
            for (int t = 0; t < 4; t++) {
                int u = rnd(nv);
                int x, z, y;
                if (deg[u] > 0 && sample_move(u, &x, &z, &y)) make_move(u, x, z, y);
            }
            cur = eval_cost();
            runBest = cur;
            stall = 0;
        }
    }

    if (cur == 0 && (!have_valid || nv > bestNv)) {
        save_best();
        have_valid = 1;
    }

    long long em = 0;
    for (int v = 0; v < bestNv; v++) em += bestDeg[v];
    printf("%d %lld\n", bestNv, em / 2);
    for (int v = 0; v < bestNv; v++)
        for (int i = 0; i < bestDeg[v]; i++)
            if (v < bestAdj[v][i]) printf("%d %d\n", v, bestAdj[v][i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
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


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    """Plateau-walking swap search for a cover of `full` by at most d candidates."""
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Repeatedly add a vertex whose neighbourhood covers all vertices within D-1 steps."""
    if D < 2:
        return n, list(edges)
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
            for att in range(4):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _local_cover(cands, ball, full, d, rng, 150, deadline)
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
    """Greedily join deficient opposite-side vertices in random order."""
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


def _run_c(d, D, seed, graph, budget):
    """Run the C tabu search from `graph` for `budget` seconds; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    if D == 1 and d >= 1:
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

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        return best

    # Target path (D >= 4, d >= 3): W(q) incidence graph, saturated, grown by
    # cover vertices, then refined by the C tabu search.
    if D >= 4 and d >= 3:
        gq = _best_gq(d)
        if gq is not None:
            gn, ge = gq
            consider(gn, ge)
            sn, se = gn, _saturate_edges(gn, ge, d, rng)
            consider(sn, se)
            cn, ce = _extend_cover(sn, se, d, D, start + 0.22 * tl, rng)
            ce = _saturate_edges(cn, ce, d, rng)
            consider(cn, ce)

        budget = start + 0.90 * tl - 1.5 - time.monotonic()
        if budget > 2.0:
            try:
                n2, e2 = _run_c(d, D, seed, best, budget)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
